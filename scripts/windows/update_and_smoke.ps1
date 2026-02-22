param(
  [ValidateSet("ci", "research")]
  [string]$Mode = "ci"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."
Set-Location $repoRoot

Write-Host "Updating repo"
git fetch origin
git pull --ff-only

Write-Host "Bootstrapping venv"
& (Join-Path $repoRoot "scripts/windows/bootstrap_venv.ps1")

Write-Host "Running smoke"
& (Join-Path $repoRoot "scripts/windows/run_sophia_smoke.ps1") -Mode $Mode
