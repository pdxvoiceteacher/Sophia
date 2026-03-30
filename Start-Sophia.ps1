Write-Host "Starting Sophia Governance API..."

cd $PSScriptRoot

if (!(Test-Path ".venv")) {
    python -m venv .venv
}

. .\.venv\Scripts\Activate.ps1

python -m pip install --upgrade pip
python -m pip install -e .
python -m pip install fastapi uvicorn

python -m sophia.api
