#!/usr/bin/env pwsh
# SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
# SPDX-License-Identifier: MIT

# Resolves the LeanCIL pin, builds its tool and the Release production assembly, then writes the method
# templates and catalogued binding sources that proofs import. -Check compares instead of writing.
# MethodTemplates.lean embeds the assembly's identity, so each machine regenerates it rather than committing it.
param([switch]$Check)
$ErrorActionPreference = 'Stop'
function Invoke([string]$failure) {
    & $args[0] $args[1..($args.Count - 1)]
    if ($LASTEXITCODE -ne 0) { throw $failure }
}
Push-Location $PSScriptRoot
try {
    Invoke 'Dependency resolution failed' lake update
    Invoke 'LeanCIL build failed' dotnet build .lake/packages/leancil/Extractor -c Release
    Invoke 'Production build failed' dotnet build ../src/Nethermind.Int256/Nethermind.Int256.csproj -c Release `
        -p:GenerateDocumentationFile=true -p:WarningsNotAsErrors=CS1591 -nowarn:CS1591
    $tool = '.lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll'
    $assembly = '../src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll'
    $value = 'Nethermind.Int256.UInt256'
    $reference = "$value&"
    $vector = 'System.Runtime.Intrinsics.Vector256`1<ulong>&'
    $binary = "$reference,$reference,$reference"
    # The module lists templates in this order; keep each method's profiles together.
    $methods = @(
        @('Add', "UInt256::AddScalar($binary,bool)", 'scalar', 'arm64-advsimd', 'x64-sse42'),
        @('PrepareAdd', "UInt256::PrepareAdd($binary,$vector,$vector,$vector,$vector)", 'x64-v3', 'x64-v4'),
        @('Subtract', "UInt256::SubtractScalar($binary)", 'scalar', 'arm64-advsimd', 'x64-sse42'),
        @('Multiply', "UInt256::Multiply($binary)", 'scalar', 'arm64-advsimd', 'x64-v3', 'x64-v4'),
        @('LeftShift', "UInt256::LeftShift(int,$reference)", 'scalar'),
        @('RightShift', "UInt256::RightShift(int,$reference)", 'scalar'),
        @('AddWide', "UInt256::Add($binary)", 'x64-v3', 'x64-v4'),
        @('AddOverflowWide', "UInt256::AddOverflow($binary)", 'x64-v3', 'x64-v4'),
        @('SubtractWide', "UInt256::SubtractImpl($binary)", 'x64-v3', 'x64-v4'))
    $extractions = foreach ($method in $methods) {
        foreach ($profile in $method[2..($method.Count - 1)]) {
            $output = "artifacts/templates/$($method[0])-$profile"
            Invoke "Extraction of $($method[0]) for $profile failed" dotnet $tool extract $assembly $method[1] `
                $output $profile --assume-initialized $value | Out-Null
            $output
        }
    }
    $mode = if ($Check) { @('--check') } else { @() }
    Invoke 'Method templates failed' dotnet $tool templates UInt256/Generated @extractions `
        --namespace UInt256Proof.Generated.Method --omit-equations --module UInt256/Generated/MethodTemplates.lean @mode
    Invoke 'Binding sources failed' dotnet $tool bindings bindings.json @mode
}
finally { Pop-Location }
