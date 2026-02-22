param()

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."

& (Join-Path $repoRoot "scripts/windows/check_no_binaries.ps1")
if ($LASTEXITCODE -ne 0) {
  exit 1
}

$pythonExe = Join-Path (Join-Path $repoRoot ".venv") "Scripts/python.exe"
if (-not (Test-Path $pythonExe)) {
  Write-Host "Missing $pythonExe. Run scripts/windows/bootstrap_venv.ps1 first."
  exit 1
}

& $pythonExe -m pytest -q tests/test_windows_ps1_param.py tests/test_no_repo_binaries.py tests/test_no_desktop_binaries.py
