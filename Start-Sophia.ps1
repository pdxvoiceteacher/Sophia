Write-Host "Starting Sophia Governance API..."

cd $PSScriptRoot

if (!(Test-Path ".venv")) {
    python -m venv .venv
}

. .\.venv\Scripts\Activate.ps1

pip install -e .
pip install fastapi uvicorn

python -m sophia.api
