Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."
$venvPath = Join-Path $repoRoot ".venv"
$pythonExe = Join-Path $venvPath "Scripts/python.exe"

if (-not (Test-Path $pythonExe)) {
  Write-Host "Creating virtualenv at $venvPath"
  python -m venv $venvPath
}

Write-Host "Upgrading pip"
& $pythonExe -m pip install --upgrade pip

Write-Host "Installing editable packages"
& $pythonExe -m pip install -e (Join-Path $repoRoot "ucc")
& $pythonExe -m pip install -e (Join-Path $repoRoot "sophia-core")
& $pythonExe -m pip install -e (Join-Path $repoRoot "python")

Write-Host "Installing API runtime dependencies"
& $pythonExe -m pip install fastapi uvicorn
