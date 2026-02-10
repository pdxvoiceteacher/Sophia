param()

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

$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$baseOutDir = Join-Path (Join-Path $repoRoot "out") ("shutdown_smoke_" + $timestamp)
$withoutWarrant = Join-Path $baseOutDir "without_warrant"
$withWarrant = Join-Path $baseOutDir "with_warrant"

Write-Host "Running shutdown smoke (without shutdown warrant) to $withoutWarrant"
& $pythonExe (Join-Path $repoRoot "tools/telemetry/run_wrapper.py") --out $withoutWarrant --quick --emit-tel --emit-tel-events
& $pythonExe (Join-Path $repoRoot "tools/sophia/resolve_mvss_policy.py") `
  --registry (Join-Path $repoRoot "governance/identity/registry_snapshots/demo_registry_snapshot.json") `
  --policy (Join-Path $repoRoot "governance/policies/demo_mvss_policy.json") `
  --stakeholder-scope global `
  --out (Join-Path $withoutWarrant "policy_resolution.json")
& $pythonExe (Join-Path $repoRoot "tools/sophia/mint_governance_bundle.py") `
  --registry (Join-Path $repoRoot "governance/identity/registry_snapshots/demo_registry_snapshot.json") `
  --policy (Join-Path $repoRoot "governance/policies/demo_mvss_policy.json") `
  --stakeholder-scope global `
  --ballot-text-primary "Approve governance bundle?" `
  --ballot-text-translation "es=¿Aprobar paquete de gobernanza?" `
  --ballot-text-translation "fr=Approuver le lot de gouvernance ?" `
  --choices yes no `
  --decision-mode pass `
  --shutdown-demo `
  --out-dir $withoutWarrant
& $pythonExe (Join-Path $repoRoot "tools/telemetry/sophia_audit.py") `
  --run-dir $withoutWarrant `
  --repo-root $repoRoot `
  --schema (Join-Path $repoRoot "schema/sophia_audit_v3.schema.json") `
  --mode research `
  --calibrate-trajectories `
  --ethics-check `
  --memory-aware `
  --audit-sophia

Write-Host "Running shutdown smoke (with shutdown warrant) to $withWarrant"
& $pythonExe (Join-Path $repoRoot "tools/telemetry/run_wrapper.py") --out $withWarrant --quick --emit-tel --emit-tel-events
& $pythonExe (Join-Path $repoRoot "tools/sophia/resolve_mvss_policy.py") `
  --registry (Join-Path $repoRoot "governance/identity/registry_snapshots/demo_registry_snapshot.json") `
  --policy (Join-Path $repoRoot "governance/policies/demo_mvss_policy.json") `
  --stakeholder-scope global `
  --out (Join-Path $withWarrant "policy_resolution.json")
& $pythonExe (Join-Path $repoRoot "tools/sophia/mint_governance_bundle.py") `
  --registry (Join-Path $repoRoot "governance/identity/registry_snapshots/demo_registry_snapshot.json") `
  --policy (Join-Path $repoRoot "governance/policies/demo_mvss_policy.json") `
  --stakeholder-scope global `
  --ballot-text-primary "Approve governance bundle?" `
  --ballot-text-translation "es=¿Aprobar paquete de gobernanza?" `
  --ballot-text-translation "fr=Approuver le lot de gouvernance ?" `
  --choices yes no `
  --decision-mode pass `
  --shutdown-demo `
  --emit-shutdown-warrant `
  --out-dir $withWarrant
& $pythonExe (Join-Path $repoRoot "tools/telemetry/sophia_audit.py") `
  --run-dir $withWarrant `
  --repo-root $repoRoot `
  --schema (Join-Path $repoRoot "schema/sophia_audit_v3.schema.json") `
  --mode research `
  --calibrate-trajectories `
  --ethics-check `
  --memory-aware `
  --audit-sophia

Write-Host "Artifacts (without warrant):"
Get-ChildItem -Path $withoutWarrant | Format-Table Name, Length
Write-Host "Artifacts (with warrant):"
Get-ChildItem -Path $withWarrant | Format-Table Name, Length
