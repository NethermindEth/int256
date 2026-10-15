[CmdletBinding()]
param(
    [string[]] $ChangedPaths = @(),
    [switch] $All
)

$ErrorActionPreference = 'Stop'
$registry = Get-Content (Join-Path $PSScriptRoot 'manifests/gates.json') -Raw | ConvertFrom-Json
$changed = @($ChangedPaths | ForEach-Object { $_.Replace('\', '/') } |
    Where-Object { $_ -and $_ -notmatch '\.(md|txt)$' -and $_ -notmatch '(^|/)(LICENSE|NOTICE|THIRD-PARTY-NOTICES)$' })
$full = $All.IsPresent
foreach ($path in $changed) {
    if ($path -match '^src/Nethermind\.Int256\.(Tests|Benchmark)/') { continue }
    if ($path -match '^src/' -or $path -match '(^|/)(global\.json|NuGet\.Config|Directory\.(Build|Packages)\..*|\.editorconfig)$' -or
        $path -eq '.github/workflows/verification.yml' -or
        ($path.StartsWith('verification/') -and $path -notmatch '\.lean$')) {
        $full = $true
    }
}

function Get-ProofSources {
    param([string] $Proof)
    $seen = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    $pending = [Collections.Generic.Stack[string]]::new()
    $pending.Push($Proof)
    while ($pending.Count -gt 0) {
        $relative = $pending.Pop()
        if (!$seen.Add("verification/$relative")) { continue }
        $path = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot $relative))
        $back = [IO.Path]::GetRelativePath($PSScriptRoot, $path)
        if ($back -eq '..' -or $back.StartsWith('..' + [IO.Path]::DirectorySeparatorChar)) {
            throw "Proof dependency escapes verification/: $relative"
        }
        if (!(Test-Path -LiteralPath $path -PathType Leaf)) { throw "Missing proof source: $relative" }
        $source = Get-Content -LiteralPath $path -Raw
        foreach ($match in [regex]::Matches($source, '(?m)^\s*(?:public\s+)?import\s+([^\r\n]+)')) {
            $imports = ($match.Groups[1].Value -split '--', 2)[0] -split '\s+'
            foreach ($module in $imports) {
                if (!$module) { continue }
                $dependency = $module.Replace('.', '/') + '.lean'
                if (Test-Path -LiteralPath (Join-Path $PSScriptRoot $dependency) -PathType Leaf) {
                    $pending.Push($dependency)
                } elseif ($module -ne 'Extracted' -and $module -notmatch '^(CIL|Lean|Std|Init)(\.|$)') {
                    throw "Unresolved consumer import: $module"
                }
            }
        }
    }
    return ,$seen
}

$selected = @(
    foreach ($gate in $registry.gates) {
        $sources = Get-ProofSources $gate.proof
        if ($full -or @($changed | Where-Object { $sources.Contains($_) }).Count -gt 0) { $gate }
    }
)
$contracts = $full -or @($changed | Where-Object { $_ -match '^verification/.*\.lean$' }).Count -gt 0
@{ contracts = $contracts; include = $selected } | ConvertTo-Json -Depth 5 -Compress
