param(
  [string]$OutRoot = "ucc\out",
  [string]$PythonExe = ""
)

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"

# Resolve repo root from this script location: ucc\notes\coherence_runs\MakeCoherenceRuns.ps1
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..")).Path
Set-Location $RepoRoot

if ([string]::IsNullOrWhiteSpace($PythonExe)) {
  $cand = Join-Path $RepoRoot "python\.venv\Scripts\python.exe"
  if (Test-Path $cand) { $PythonExe = $cand } else { $PythonExe = "python" }
}

Write-Host "RepoRoot: $RepoRoot"
Write-Host "Python:   $PythonExe"
Write-Host "OutRoot:  $OutRoot"

Start-Transcript -Path (Join-Path $PSScriptRoot "coherence_runs.log") -Append | Out-Null

function RunPy {
  param([Parameter(ValueFromRemainingArguments=$true)][string[]]$CmdArgs)

  if (-not $CmdArgs -or $CmdArgs.Count -eq 0) {
    throw "RunPy called with no args (would launch interactive python)."
  }

  Write-Host ("`n>> " + $PythonExe + " " + ($CmdArgs -join " "))
  & $PythonExe @CmdArgs
  if ($LASTEXITCODE -ne 0) {
    throw "Command failed with exit code $LASTEXITCODE"
  }
}

# Ensure upstream outputs exist (these are what sources.csv points at)
RunPy -m ucc.cli run ucc/modules/helmholtz_compare.yml --input ucc/tasks/helmholtz_compare_sample.json --outdir "$OutRoot/helmholtz_compare_sample"
RunPy -m ucc.cli run ucc/modules/tches_compare.yml --input ucc/tasks/tches_compare_sample.json --outdir "$OutRoot/tches_compare_sample"
RunPy -m ucc.cli run ucc/modules/quantum_anchor_coverage.yml --input ucc/tasks/quantum_anchor_task.json --outdir "$OutRoot/quantum_anchor_sample"

# Build coherence artifacts from committed run packs
RunPy -m ucc.make_coherence_artifact --out ucc/tasks/coherence_runs/helmholtz_coherence.json --id helmholtz-001 --domain research --question "Audit Helmholtz artifacts" --answer_md ucc/notes/coherence_runs/helmholtz_writeup.md --claims_csv ucc/notes/coherence_runs/helmholtz_claims.csv --sources_csv ucc/notes/coherence_runs/helmholtz_sources.csv --evidence_link https://github.com/pdxvoiceteacher/CoherenceLattice --reporting_primary "github issues" --reporting_escalation maintainers
RunPy -m ucc.make_coherence_artifact --out ucc/tasks/coherence_runs/tches_coherence.json --id tches-001 --domain research --question "Audit TCHES artifacts" --answer_md ucc/notes/coherence_runs/tches_writeup.md --claims_csv ucc/notes/coherence_runs/tches_claims.csv --sources_csv ucc/notes/coherence_runs/tches_sources.csv --evidence_link https://github.com/pdxvoiceteacher/CoherenceLattice --reporting_primary "github issues" --reporting_escalation maintainers
RunPy -m ucc.make_coherence_artifact --out ucc/tasks/coherence_runs/quantum_coherence.json --id quantum-001 --domain research --question "Audit Quantum anchor artifacts" --answer_md ucc/notes/coherence_runs/quantum_writeup.md --claims_csv ucc/notes/coherence_runs/quantum_claims.csv --sources_csv ucc/notes/coherence_runs/quantum_sources.csv --evidence_link https://github.com/pdxvoiceteacher/CoherenceLattice --reporting_primary "github issues" --reporting_escalation maintainers

# Run coherence audits
RunPy -m ucc.cli run ucc/modules/coherence_audit.yml --input ucc/tasks/coherence_runs/helmholtz_coherence.json --outdir "$OutRoot/coherence_helmholtz"
RunPy -m ucc.cli run ucc/modules/coherence_audit.yml --input ucc/tasks/coherence_runs/tches_coherence.json --outdir "$OutRoot/coherence_tches"
RunPy -m ucc.cli run ucc/modules/coherence_audit.yml --input ucc/tasks/coherence_runs/quantum_coherence.json --outdir "$OutRoot/coherence_quantum"

Write-Host "`n✅ Done. See:"
Write-Host " - $OutRoot/coherence_helmholtz"
Write-Host " - $OutRoot/coherence_tches"
Write-Host " - $OutRoot/coherence_quantum"

Stop-Transcript | Out-Null