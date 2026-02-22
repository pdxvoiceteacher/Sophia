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
& $pip install -r requirements.txt

Write-Host "Bootstrap complete. Activate with: $Venv\\Scripts\\Activate.ps1"
