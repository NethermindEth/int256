[CmdletBinding()]
param(
    [ValidateSet('Contracts', 'Extract', 'Verify')]
    [string] $Action = 'Contracts',
    [string] $Method = 'Add',
    [string] $Profile = 'scalar',
    [string] $Proof,
    [string] $Theorem
)

$ErrorActionPreference = 'Stop'
function Invoke-Checked {
    param([string] $Command, [string[]] $Arguments)
    & $Command @Arguments
    if ($LASTEXITCODE -ne 0) { throw "$Command failed with exit code $LASTEXITCODE" }
}

Push-Location $PSScriptRoot
try {
    Invoke-Checked lake @('update')
    if ($Action -eq 'Contracts') {
        Invoke-Checked lake @('build')
        Invoke-Checked lake @('env', 'lean', 'Audit.lean')
        Write-Host 'UInt256 contracts and supporting lemmas checked. No compiled-method certificate was produced.'
        return
    }

    $inventory = Get-Content manifests/targets.json -Raw | ConvertFrom-Json
    $target = @($inventory.methods | Where-Object id -EQ $Method)
    if ($target.Count -ne 1) { throw "Unknown or ambiguous method ID: $Method. See manifests/targets.json." }
    if ($Profile -notmatch '^[a-zA-Z0-9-]+$') { throw 'Expected a profile name.' }
    $profileArgument = $Profile
    if (Test-Path "manifests/profiles/$Profile.json") { $profileArgument = "@manifests/profiles/$Profile.json" }
    $output = "artifacts/$Method/$Profile"
    # A failed fresh extraction must not leave an old certificate available.
    if (Test-Path "$output/verified.json") { Remove-Item -LiteralPath "$output/verified.json" }
    if ($Action -eq 'Verify') {
        if ([string]::IsNullOrWhiteSpace($Proof) -or [string]::IsNullOrWhiteSpace($Theorem)) {
            throw 'Verify requires -Proof (relative to verification/) and -Theorem. No compiled-method proof is registered yet.'
        }
        if (!(Test-Path -LiteralPath $Proof -PathType Leaf)) { throw "Proof file not found: $Proof" }
    }
    Invoke-Checked dotnet @('build', '.lake/packages/leancil/Extractor', '-c', 'Release')
    Invoke-Checked dotnet @('build', '../src/Nethermind.Int256/Nethermind.Int256.csproj', '-c', 'Release')
    Invoke-Checked dotnet @('.lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll',
        'extract', '../src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll',
        $target[0].signature, $output, $profileArgument,
        '--assume-initialized', 'Nethermind.Int256.UInt256')
    if ($Action -eq 'Verify') {
        Invoke-Checked dotnet @('.lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll',
            'verify', $output, '--proof', $Proof, '--theorem', $Theorem,
            '--proof-root', $PSScriptRoot)
    }
}
finally { Pop-Location }
