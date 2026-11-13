#!/usr/bin/env pwsh
# SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
# SPDX-License-Identifier: MIT

# Runs each Bitwise mutation assembly that a `leancil gates` results file rejected, with and without hardware
# intrinsics, so the refutation witnesses match what .NET computes on this machine.
param([Parameter(Mandatory)][string]$Results)
$ErrorActionPreference = 'Stop'
$expectedLines = @{ BitwiseWrongOperator = 8; BitwiseEarlyStore = 4 }
$rows = @((Get-Content -LiteralPath $Results -Raw | ConvertFrom-Json).rows | Where-Object {
    $expectedLines.ContainsKey($_.variant) -and $_.gate -match '^(Operator)?(And|Or|Xor|Not)-' })
if ($rows.Count -eq 0) { 'No Bitwise mutation rows in this group.'; return }
$failed = @($rows | Where-Object status -ne 'rejected')
if ($failed.Count -gt 0) { throw "Bitwise mutation rows did not pass: $(($failed | ForEach-Object id) -join ', ')" }
# Rows of one variant share a build, so each distinct assembly runs once.
$assemblies = @{}
foreach ($row in $rows) {
    $output = [IO.Path]::GetFullPath($row.output, $PSScriptRoot)
    $identity = Get-Content -LiteralPath (Join-Path $output 'identity.json') -Raw | ConvertFrom-Json
    $assembly = [IO.Path]::GetFullPath($identity.assemblyPath, $output)
    $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath $assembly).Hash
    if ($hash -ne $identity.assemblySha256.ToUpperInvariant()) { throw "$($row.id): $assembly no longer matches its extraction" }
    $assemblies["$($row.variant)|$hash"] = @{ Variant = $row.variant; Assembly = $assembly; Hash = $hash }
}
foreach ($entry in $assemblies.Values) {
    $build = Join-Path $PSScriptRoot "artifacts/native-witness/$($entry.Variant)-$($entry.Hash.Substring(0, 12))"
    dotnet build (Join-Path $PSScriptRoot 'Tests/Fixtures/Bitwise/NativeWitness.csproj') -c Release `
        "-p:FixtureAssembly=$($entry.Assembly)" "-p:BaseOutputPath=$build/bin/" "-p:BaseIntermediateOutputPath=$build/obj/" `
        -p:EnforceCodeStyleInBuild=true -p:GenerateDocumentationFile=true -p:WarningsAsErrors=IDE0005 -v:q
    if ($LASTEXITCODE -ne 0) { throw "NativeWitness build failed for $($entry.Variant)" }
    $binaries = "$build/bin/Release/net10.0"
    if ((Get-FileHash -Algorithm SHA256 -LiteralPath "$binaries/Nethermind.Int256.dll").Hash -ne $entry.Hash) {
        throw "NativeWitness resolved a different fixture assembly for $($entry.Variant)"
    }
    foreach ($intrinsics in '1', '0') {
        $env:DOTNET_EnableHWIntrinsic = $intrinsics
        $lines = @(dotnet "$binaries/NativeWitness.dll" $entry.Variant)
        $code = $LASTEXITCODE
        Remove-Item Env:DOTNET_EnableHWIntrinsic
        $lines
        $passed = @($lines | Where-Object { $_ -like "PASS native */$($entry.Variant)" }).Count
        if ($code -ne 0 -or $passed -ne $expectedLines[$entry.Variant]) {
            throw "NativeWitness $($entry.Variant) with EnableHWIntrinsic=${intrinsics}: exit $code, " +
                "$passed of $($expectedLines[$entry.Variant]) witnesses"
        }
    }
}
