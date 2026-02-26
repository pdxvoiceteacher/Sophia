param(
    [string]$Venv = ".venv"
)

$ErrorActionPreference = "Stop"

if (-not (Get-Command python -ErrorAction SilentlyContinue)) {
    throw "python not found on PATH"
}

python -m venv $Venv

$pip = Join-Path $Venv "Scripts/pip.exe"
if (-not (Test-Path $pip)) {
    throw "pip not found in virtual environment: $pip"
}

& $pip install --upgrade pip
& $pip install -r python/tools/requirements-telemetry.txt
& $pip install -e ./python -e ./ucc -e ./sophia-core -e ./tools/coherenceledger_bootstrap

# core smoke set for telemetry/runner surfaces
& $pip install pytest
& (Join-Path $Venv "Scripts/python.exe") -m pytest -q tests/test_run_wrapper_evidence_paths.py tests/test_epoch_real_runner.py

Write-Host "Bootstrap complete. Activate with: $Venv\Scripts\Activate.ps1"
