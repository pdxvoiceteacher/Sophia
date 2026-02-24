param()

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."
Set-Location $repoRoot

Write-Host "Bootstrapping venv"
& (Join-Path $repoRoot "scripts/windows/bootstrap_venv.ps1")

Write-Host "Sanitizing repo + preflight"
& (Join-Path $repoRoot "scripts/windows/sanitize_repo.ps1")

Write-Host "Running governance smoke (research mode)"
& (Join-Path $repoRoot "scripts/windows/run_governance_smoke.ps1") -Mode research

Write-Host "Running shutdown smoke"
& (Join-Path $repoRoot "scripts/windows/run_shutdown_smoke.ps1")

Write-Host "Launching full stack"
& (Join-Path $repoRoot "scripts/windows/run_full_stack.ps1")
