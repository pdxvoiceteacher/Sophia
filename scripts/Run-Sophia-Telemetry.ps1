param(
  [string]$OutRoot = "C:\Sophia\runs",
  [int]$Perturbations = 3,
  [switch]$Quick = $true,
  [switch]$EmitTelEvents = $true
)

$ErrorActionPreference = "Stop"
$RepoRoot = (Resolve-Path ".").Path

if (-not (Test-Path ".\.venv\Scripts\python.exe")) {
  py -3 -m venv .\.venv
}

$Py = (Resolve-Path ".\.venv\Scripts\python.exe").Path
& $Py -m pip install -U pip setuptools wheel | Out-Host

if (Test-Path ".\python\tools\requirements-telemetry.txt") {
  & $Py -m pip install -r ".\python\tools\requirements-telemetry.txt" | Out-Host
}

foreach ($proj in @(".\python", ".\ucc", ".\tools\coherenceledger_bootstrap")) {
  if (Test-Path "$proj\pyproject.toml") {
    & $Py -m pip install -e $proj | Out-Host
  }
}

& $Py -m pip install pytest | Out-Host
& $Py -m pytest -q tests/test_run_wrapper_evidence_paths.py tests/test_secure_swarm_crypto.py tests/test_secure_swarm_schemas.py tests/test_epoch_real_runner.py | Out-Host

$stamp = Get-Date -Format "yyyyMMdd-HHmmss"
$outdir = Join-Path $OutRoot $stamp
New-Item -ItemType Directory -Force -Path $outdir | Out-Null
$env:PYTHONPATH = $RepoRoot

$cmd = @("tools\telemetry\run_wrapper.py", "--out", $outdir, "--perturbations", "$Perturbations")
if ($Quick) { $cmd += "--quick" }
if ($EmitTelEvents) { $cmd += "--emit-tel-events" }

Write-Host "Running: $Py $($cmd -join ' ')"
& $Py @cmd | Out-Host

Write-Host ""
Write-Host "Artifacts in: $outdir"
Get-ChildItem $outdir | Format-Table -AutoSize

if (Test-Path (Join-Path $outdir "consensus_summary.json")) {
  Write-Host ""
  Write-Host "consensus_summary.json:"
  Get-Content (Join-Path $outdir "consensus_summary.json")
}
