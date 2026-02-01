param(
  [int]$Port = 8001
)

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

Write-Host "Starting Standards Gateway on port $Port"
$gatewayJob = Start-Job -ScriptBlock {
  param($pythonExe, $port)
  & $pythonExe -m uvicorn tools.sophia.standards_api:app --port $port
} -ArgumentList $pythonExe, $Port

try {
  Start-Sleep -Seconds 2
  & (Join-Path $repoRoot "scripts/windows/run_governance_smoke.ps1")
  Write-Host "Viewer URL: http://localhost:$Port/sophia/viewer"
  Write-Host "API URL: http://localhost:$Port/.well-known/sophia.json"
} finally {
  Write-Host "Stopping Standards Gateway job"
  Stop-Job $gatewayJob | Out-Null
  Remove-Job $gatewayJob | Out-Null
}
