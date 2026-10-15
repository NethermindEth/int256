$ErrorActionPreference = 'Stop'
$registry = Get-Content (Join-Path $PSScriptRoot 'manifests/gates.json') -Raw | ConvertFrom-Json

function Assert-Selection {
    param([string[]] $Paths, [string[]] $Methods, [bool] $Contracts)
    $actual = & (Join-Path $PSScriptRoot 'SelectGates.ps1') -ChangedPaths $Paths | ConvertFrom-Json
    $expectedNames = @($Methods | Sort-Object) -join ','
    $actualNames = @($actual.include.method | Sort-Object) -join ','
    if ($actual.contracts -ne $Contracts -or $actualNames -ne $expectedNames) {
        throw "Unexpected selection for $($Paths -join ', '): $($actual | ConvertTo-Json -Compress -Depth 5)"
    }
}

Assert-Selection @('README.md', 'verification/README.md', 'LICENSE') @() $false
Assert-Selection @('verification/proofs/AddScalar.lean') @('Add') $true
Assert-Selection @('verification/UInt256/Methods/Equality/ScalarSafetyContract.lean') `
    @('EqUInt256UInt256', 'EqualsUInt256Ref', 'NeUInt256UInt256') $true
Assert-Selection @('verification/UnusedProof.lean') @() $true
Assert-Selection @('src/Nethermind.Int256.Tests/UInt256Tests.cs') @() $false
Assert-Selection @('src/Nethermind.Int256.Benchmark/AddBenchmarks.cs') @() $false
Assert-Selection @('src/Nethermind.Int256/UInt256.cs') @($registry.gates.method) $true
Assert-Selection @('verification/manifests/gates.json') @($registry.gates.method) $true

$all = & (Join-Path $PSScriptRoot 'SelectGates.ps1') -All | ConvertFrom-Json
if (!$all.contracts -or @($all.include).Count -ne @($registry.gates).Count) {
    throw 'Full verification did not select every registered gate'
}
'Verification gate selection checks passed.'
