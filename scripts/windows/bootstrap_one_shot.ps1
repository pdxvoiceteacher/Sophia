param(
  [string]$PythonExe = "python",
  [string]$VenvDir = ".venv",
  [string]$OutDir = "out/windows_smoke"
)

$ErrorActionPreference = "Stop"
$repoRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
Set-Location $repoRoot

& $PythonExe -m venv $VenvDir
$py = Join-Path $repoRoot "$VenvDir/Scripts/python.exe"

& $py -m pip install --upgrade pip
& $py -m pip install -r .\python\tools\requirements-telemetry.txt
& $py -m pip install -e .\python
& $py -m pip install -e .\ucc

& $py -m pytest -q tests/test_run_wrapper_evidence_paths.py tests/test_secure_swarm_crypto.py tests/test_secure_swarm_schemas.py tests/test_epoch_real_runner.py tests/test_run_wrapper_invocation.py

Write-Host "Bootstrap complete. Example run:"
Write-Host "$py tools/telemetry/run_wrapper.py --out $OutDir --quick --perturbations 1 --simulate-peers 2 --simulate-peer-weight-mode uniform"
