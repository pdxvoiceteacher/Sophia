param()

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path "."
$utf8NoBom = New-Object System.Text.UTF8Encoding($false)

$failed = @()

Get-ChildItem -Path (Join-Path $repoRoot "scripts/windows") -Filter "*.ps1" | ForEach-Object {
  $path = $_.FullName
  $content = Get-Content $path -Raw
  $content = $content -replace "^\uFEFF", ""
  $content = $content -replace "^\s*(?=param\()", ""
  [System.IO.File]::WriteAllText($path, $content, $utf8NoBom)
}

& (Join-Path $repoRoot "scripts/windows/check_no_binaries.ps1")
if ($LASTEXITCODE -ne 0) {
  $failed += "check_no_binaries.ps1"
}

$pythonExe = Join-Path (Join-Path $repoRoot ".venv") "Scripts/python.exe"
if (-not (Test-Path $pythonExe)) {
  Write-Host "Missing $pythonExe. Run scripts/windows/bootstrap_venv.ps1 first."
  exit 1
}

& $pythonExe -m pytest -q tests/test_windows_ps1_param.py tests/test_no_repo_binaries.py tests/test_no_desktop_binaries.py
if ($LASTEXITCODE -ne 0) {
  $failed += "pytest"
}

if ($failed.Count -gt 0) {
  Write-Host "Preflight failed: $($failed -join ', ')"
  exit 1
}

Write-Host "OK to PR"
