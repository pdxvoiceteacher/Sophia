Write-Host "Starting Sophia Governance API..."

cd $PSScriptRoot

function Test-HttpOk {
    param([string]$Uri)
    try {
        $r = Invoke-WebRequest -UseBasicParsing -Uri $Uri -TimeoutSec 3
        return ($r.StatusCode -ge 200 -and $r.StatusCode -lt 300)
    } catch {
        return $false
    }
}

if (Test-HttpOk -Uri "http://127.0.0.1:8000/health") {
    Write-Host "[Sophia] already running on 127.0.0.1:8000"
    exit 0
}

if (!(Test-Path ".venv")) {
    python -m venv .venv
}

. .\.venv\Scripts\Activate.ps1

python -m pip install --upgrade pip
python -m pip install -e .
python -m pip install fastapi uvicorn

python -m sophia.api
