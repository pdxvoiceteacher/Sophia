param()

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."
$pythonExe = Join-Path (Join-Path $repoRoot ".venv") "Scripts/python.exe"

if (-not (Test-Path $pythonExe)) {
  Write-Host "Missing $pythonExe. Run scripts/windows/bootstrap_venv.ps1 first."
  exit 1
}

& $pythonExe (Join-Path $repoRoot "scripts/check_no_binaries.py")
