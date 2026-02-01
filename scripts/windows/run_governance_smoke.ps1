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
$outDir = Join-Path (Join-Path $repoRoot "out") ("gov_smoke_" + $timestamp)

Write-Host "Running governance smoke to $outDir"
& $pythonExe (Join-Path $repoRoot "tools/telemetry/run_wrapper.py") --out $outDir --quick --emit-tel --emit-tel-events

& $pythonExe (Join-Path $repoRoot "tools/sophia/resolve_mvss_policy.py") `
  --registry (Join-Path $repoRoot "governance/identity/registry_snapshots/demo_registry_snapshot.json") `
  --policy (Join-Path $repoRoot "governance/policies/demo_mvss_policy.json") `
  --stakeholder-scope global `
  --out (Join-Path $outDir "policy_resolution.json")

& $pythonExe (Join-Path $repoRoot "tools/sophia/mint_governance_bundle.py") `
  --registry (Join-Path $repoRoot "governance/identity/registry_snapshots/demo_registry_snapshot.json") `
  --policy (Join-Path $repoRoot "governance/policies/demo_mvss_policy.json") `
  --stakeholder-scope global `
  --ballot-text-primary "Approve governance bundle?" `
  --ballot-text-translation "es=¿Aprobar paquete de gobernanza?" `
  --ballot-text-translation "fr=Approuver le lot de gouvernance ?" `
  --choices yes no `
  --out-dir $outDir

& $pythonExe (Join-Path $repoRoot "tools/telemetry/sophia_audit.py") `
  --run-dir $outDir `
  --repo-root $repoRoot `
  --schema (Join-Path $repoRoot "schema/sophia_audit_v3.schema.json") `
  --mode research `
  --calibrate-trajectories `
  --ethics-check `
  --memory-aware `
  --audit-sophia

Write-Host "Artifacts:"
Get-ChildItem -Path $outDir | Format-Table Name, Length
