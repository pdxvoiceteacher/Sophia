param(
    [switch]$RebuildVenv = $false
)

$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot

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

if ($RebuildVenv -and (Test-Path ".venv")) {
    Remove-Item -Recurse -Force ".venv"
}

if (!(Test-Path ".venv")) {
    python -m venv .venv
}

. .\.venv\Scripts\Activate.ps1
python -m pip install --upgrade pip
python -m pip install -e .

$cohRoot = Resolve-Path (Join-Path $PSScriptRoot "..\CoherenceLattice")
$bridgeRoot = Join-Path $cohRoot.Path "bridge"
New-Item -ItemType Directory -Force $bridgeRoot | Out-Null

$env:COHERENCE_LATTICE_ROOT = $cohRoot.Path
$env:TRIADIC_BRIDGE_ROOT = $bridgeRoot

Write-Host "[Sophia] starting API on 127.0.0.1:8000"
python -m uvicorn sophia.api.server:app --host 127.0.0.1 --port 8000
