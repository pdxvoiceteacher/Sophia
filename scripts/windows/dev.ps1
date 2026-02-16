param(
  [switch]$LaunchFullStack
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."
if (-not (Test-Path (Join-Path $repoRoot "scripts/windows/dev_up.ps1"))) {
  Write-Host "Run this from the repository root (scripts/windows/dev_up.ps1 not found)."
  exit 1
}

Write-Host "Repo root: $repoRoot"
Write-Host "Next: bootstrap -> sanitize -> governance smoke -> shutdown smoke"
if ($LaunchFullStack) {
  Write-Host "Full stack launch enabled."
} else {
  Write-Host "Use -LaunchFullStack to start run_full_stack at the end."
}

& (Join-Path $repoRoot "scripts/windows/bootstrap_venv.ps1")
& (Join-Path $repoRoot "scripts/windows/sanitize_repo.ps1")
& (Join-Path $repoRoot "scripts/windows/run_governance_smoke.ps1") -Mode research
& (Join-Path $repoRoot "scripts/windows/run_shutdown_smoke.ps1")

if ($LaunchFullStack) {
  & (Join-Path $repoRoot "scripts/windows/run_full_stack.ps1")
}
