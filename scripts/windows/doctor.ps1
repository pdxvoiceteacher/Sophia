param()

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path ".").Path
$expectedMarker = Join-Path $repoRoot "scripts/windows/sanitize_repo.ps1"
Write-Host "[doctor] repo root: $repoRoot"

if (-not (Test-Path $expectedMarker)) {
  Write-Host "[doctor] ERROR: run this from the Sophia repo root (missing scripts/windows/sanitize_repo.ps1)."
  exit 1
}

$pythonExe = Join-Path $repoRoot ".venv\Scripts\python.exe"
if (Test-Path $pythonExe) {
  Write-Host "[doctor] python ok: $pythonExe"
} else {
  Write-Host "[doctor] python missing: $pythonExe"
  Write-Host "[doctor] next: & .\scripts\windows\bootstrap_venv.ps1"
}

Write-Host "[doctor] git status --porcelain"
& git status --porcelain

$checkNoBinaries = Join-Path $repoRoot "scripts/windows/check_no_binaries.ps1"
Write-Host "[doctor] running: $checkNoBinaries"
& $checkNoBinaries

Write-Host "[doctor] next commands:"
Write-Host "  1) Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass"
Write-Host "  2) & .\scripts\windows\sanitize_repo.ps1"
Write-Host "  3) & .\scripts\windows\preflight_pr.ps1"
