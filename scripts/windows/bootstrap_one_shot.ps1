param(
  [string]$PythonExe = "python",
  [string]$VenvDir = ".venv",
  [string]$OutDir = "out/telemetry_smoke"
)

$ErrorActionPreference = "Stop"
$repoRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
Set-Location $repoRoot

& $PythonExe -m venv $VenvDir
$py = Join-Path $repoRoot "$VenvDir/Scripts/python.exe"

& $py -m pip install --upgrade pip
& $py -m pip install -r requirements.txt -e ./tools/coherenceledger_bootstrap hypothesis httpx

& $py -m pytest -q tests/test_run_wrapper_invocation.py tests/test_run_wrapper_evidence_paths.py
& $py tools/telemetry/run_wrapper.py --out $OutDir --quick --perturbations 1 --emit-tel --emit-tel-events

Write-Host "Artifacts written under: $OutDir"
