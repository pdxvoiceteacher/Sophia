Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$venvPath = ".venv"
$pythonExe = Join-Path $venvPath "Scripts/python.exe"

if (-not (Test-Path $pythonExe)) {
  Write-Host "Missing $pythonExe. Run scripts/dev_bootstrap.ps1 first."
  exit 1
}

$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$outDir = Join-Path "out" ("smoke_" + $timestamp)

Write-Host "Running KONOMI smoke to $outDir"
& $pythonExe tools/telemetry/run_wrapper.py --out $outDir --quick --emit-tel --emit-tel-events

Write-Host "Building epistemic graph"
& $pythonExe tools/telemetry/build_epistemic_graph.py --run-dir $outDir --repo-root .

Write-Host "Running Sophia audit"
& $pythonExe tools/telemetry/sophia_audit.py --run-dir $outDir --repo-root .

Write-Host "Smoke run complete: $outDir"
