param(
    [switch]$RebuildVenv = $false,
    [switch]$RunTests = $false
)

$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot

if ($RebuildVenv -and (Test-Path ".venv")) {
    Remove-Item -Recurse -Force ".venv"
}

if (!(Test-Path ".venv")) {
    python -m venv .venv
}

. .\.venv\Scripts\Activate.ps1
python -m pip install --upgrade pip
python -m pip install -e .

if (Test-Path ".\requirements-dev.txt") {
    python -m pip install -r .\requirements-dev.txt
}

if ($RunTests) {
    python -m pytest -q
}
