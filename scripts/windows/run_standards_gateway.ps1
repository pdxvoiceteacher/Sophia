param(
  [int]$Port = 8001
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."

Write-Host "Bootstrapping venv"
& (Join-Path $repoRoot "scripts/windows/bootstrap_venv.ps1")

$venvPath = Join-Path $repoRoot ".venv"
$pythonExe = Join-Path $venvPath "Scripts/python.exe"

if (-not (Test-Path $pythonExe)) {
  Write-Host "Missing $pythonExe. Run scripts/windows/bootstrap_venv.ps1 first."
  exit 1
}

Write-Host "Starting Sophia Standards Gateway on port $Port"
& $pythonExe -m uvicorn tools.sophia.standards_api:app --port $Port
