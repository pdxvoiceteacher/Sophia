param(
  [ValidateSet("ci", "research")]
  [string]$Mode = "ci"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."
$venvPath = Join-Path $repoRoot ".venv"
$pythonExe = Join-Path $venvPath "Scripts/python.exe"

if (-not (Test-Path $pythonExe)) {
  Write-Host "Missing $pythonExe. Run scripts/windows/bootstrap_venv.ps1 first."
  exit 1
}

$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$outDir = Join-Path (Join-Path $repoRoot "out") ("smoke_" + $timestamp)

Write-Host "Running KONOMI smoke to $outDir"
& $pythonExe (Join-Path $repoRoot "tools/telemetry/run_wrapper.py") --out $outDir --quick --emit-tel --emit-tel-events

Write-Host "Building epistemic graph"
& $pythonExe (Join-Path $repoRoot "tools/telemetry/build_epistemic_graph.py") --run-dir $outDir --repo-root $repoRoot

$schemaPath = Join-Path $repoRoot "schema/sophia_audit.schema.json"
$auditArgs = @(
  (Join-Path $repoRoot "tools/telemetry/sophia_audit.py"),
  "--run-dir", $outDir,
  "--repo-root", $repoRoot,
  "--schema", $schemaPath
)

if ($Mode -eq "research") {
  $schemaPath = Join-Path $repoRoot "schema/sophia_audit_v3.schema.json"
  $auditArgs = @(
    (Join-Path $repoRoot "tools/telemetry/sophia_audit.py"),
    "--run-dir", $outDir,
    "--repo-root", $repoRoot,
    "--schema", $schemaPath,
    "--calibrate-trajectories",
    "--ethics-check",
    "--memory-aware",
    "--audit-sophia",
    "--mode", "research"
  )
}

Write-Host "Running Sophia audit ($Mode)"
& $pythonExe @auditArgs

Write-Host "Artifacts:"
Get-ChildItem -Path $outDir | Format-Table Name, Length
