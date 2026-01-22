Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$venvPath = ".venv"
$pythonExe = Join-Path $venvPath "Scripts/python.exe"

if (-not (Test-Path $pythonExe)) {
  Write-Host "Creating virtualenv at $venvPath"
  python -m venv $venvPath
}

Write-Host "Upgrading pip"
& $pythonExe -m pip install --upgrade pip

Write-Host "Installing editable packages"
& $pythonExe -m pip install -e .\ucc
& $pythonExe -m pip install -e .\sophia-core
& $pythonExe -m pip install -e .\python
