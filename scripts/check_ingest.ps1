Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$pythonExe = ".\\.venv\\Scripts\\python.exe"
if (-not (Test-Path $pythonExe)) {
  Write-Host "Missing $pythonExe. Run scripts/dev_bootstrap.ps1 first."
  exit 1
}

& $pythonExe -c "import json; p=r'examples/submission_demo/ingest_report.json'; d=json.load(open(p,'r',encoding='utf-8')); bad=[r for r in d.get('results',[]) if r.get('status')!='ok']; print('INGEST OK' if not bad else 'INGEST FAIL'); print(bad)"
