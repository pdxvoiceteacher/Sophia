param(
  [string]$WorkflowPath = ".github/workflows/ci.yml"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Say($msg) { Write-Host $msg -ForegroundColor Cyan }
function Warn($msg) { Write-Host $msg -ForegroundColor Yellow }
function Ok($msg) { Write-Host $msg -ForegroundColor Green }
function Fail($msg) { Write-Host $msg -ForegroundColor Red; exit 1 }

if (!(Test-Path $WorkflowPath)) {
  Fail "Missing workflow file: $WorkflowPath"
}

$backup = "$WorkflowPath.bak_" + (Get-Date -Format "yyyyMMdd_HHmmss")
Copy-Item $WorkflowPath $backup -Force
Say "Backup: $backup"

$lines = Get-Content $WorkflowPath

# --- Step blocks to insert (YAML indentation assumes inside steps:) ---
$blockTelemetry = @"
      - name: Telemetry smoke (wrapper, ΔS/Λ perturbations)
        run: .venv/bin/python tools/telemetry/run_wrapper.py --out out/telemetry_smoke --quick --perturbations 3

      - name: Validate telemetry (quality gates incl ΔS/Λ)
        run: .venv/bin/python tools/telemetry/validate_run.py out/telemetry_smoke/telemetry.json --min-psi 0.80 --min-t 0.80 --min-es 0.80 --max-lambda 0.05 --max-deltas 0.05

      - name: Compare telemetry vs baseline
        run: .venv/bin/python tools/telemetry/compare_runs.py tests/baselines/telemetry_smoke.baseline.json out/telemetry_smoke/telemetry.json

      - name: Upload telemetry artifacts
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: telemetry_smoke
          path: out/telemetry_smoke
"@

$blockStatePolicy = @"
      - name: State estimate (sensor fusion)
        run: .venv/bin/python tools/telemetry/state_estimator.py --telemetry out/telemetry_smoke/telemetry.json --perturbations out/telemetry_smoke/perturbations.json --out out/telemetry_smoke/state_estimate.json

      - name: Validate state estimate schema
        run: .venv/bin/python tools/telemetry/validate_state.py out/telemetry_smoke/state_estimate.json

      - name: Control policy (Es->Lambda->T)
        run: .venv/bin/python tools/telemetry/policy.py --state out/telemetry_smoke/state_estimate.json --out out/telemetry_smoke/control_decision.json

      - name: Validate control decision schema
        run: .venv/bin/python tools/telemetry/validate_decision.py out/telemetry_smoke/control_decision.json
"@

$blockProposal = @"
      - name: Enforce policy gate (Es->Lambda->T)
        run: .venv/bin/python tools/telemetry/enforce_policy_gate.py --decision out/telemetry_smoke/control_decision.json --allow-slow

      - name: Emit change proposal (proposal-only)
        run: .venv/bin/python tools/telemetry/propose_change.py --run-dir out/telemetry_smoke --telemetry out/telemetry_smoke/telemetry.json --state out/telemetry_smoke/state_estimate.json --decision out/telemetry_smoke/control_decision.json --out out/telemetry_smoke/change_proposal.json

      - name: Validate change proposal schema
        run: .venv/bin/python tools/telemetry/validate_proposal.py out/telemetry_smoke/change_proposal.json
"@

function Contains([string]$haystack, [string]$needle) {
  return ($haystack -match [regex]::Escape($needle))
}

$text = ($lines -join "`n")

# Helper: remove duplicate telemetry blocks (older ones) by markers
function Remove-DuplicateTelemetry([string]$t) {
  # If there are multiple occurrences of "Telemetry smoke", keep the first block and remove later ones.
  $matches = [regex]::Matches($t, "(?m)^\s*-\s+name:\s+Telemetry smoke")
  if ($matches.Count -le 1) { return $t }

  Warn "Detected multiple Telemetry smoke blocks; removing duplicates (keeping first)."
  # crude remove: remove everything from second occurrence up to the next "Upload telemetry artifacts" block end
  $secondIndex = $matches[1].Index
  $tail = $t.Substring($secondIndex)

  $end = [regex]::Match($tail, "(?ms)^\\s*-\\s+name:\\s+Upload telemetry artifacts.*?^\\s*(?=-\\s+name:|$)", [System.Text.RegularExpressions.RegexOptions]::Multiline)
  if ($end.Success) {
    $removeLen = $end.Length
    return $t.Remove($secondIndex, $removeLen)
  }
  return $t
}

$text = Remove-DuplicateTelemetry $text

# Insert telemetry block after "Run UCC tests" step (marker: '- name: Run UCC tests' OR the pytest command line)
if (-not (Contains $text "Telemetry smoke (wrapper, ΔS/Λ perturbations)")) {
  $marker1 = "name: Run UCC tests"
  if ($text -match [regex]::Escape($marker1)) {
    # Insert after the blank line following that step
    $lines2 = $text -split "`n"
    $out = New-Object System.Collections.Generic.List[string]
    $inserted = $false
    for ($i=0; $i -lt $lines2.Count; $i++) {
      $out.Add($lines2[$i])
      if (-not $inserted -and $lines2[$i] -match "^\s*-\s+name:\s+Run UCC tests\s*$") {
        # scan until blank line then insert telemetry block
        $i++
        while ($i -lt $lines2.Count) {
          $out.Add($lines2[$i])
          if ($lines2[$i].Trim() -eq "") { break }
          $i++
        }
        foreach ($l in ($blockTelemetry -split "`r?`n")) { $out.Add($l) }
        $inserted = $true
      }
    }
    $text = ($out -join "`n")
    Ok "Inserted telemetry block after Run UCC tests."
  } else {
    Warn "Could not find 'Run UCC tests' marker; skipping telemetry block insertion."
  }
} else {
  Ok "Telemetry block already present; skipping."
}

# Insert state/policy block before "Upload telemetry artifacts"
if (-not (Contains $text "State estimate (sensor fusion)")) {
  if ($text -match "(?m)^\s*-\s+name:\s+Upload telemetry artifacts") {
    $text = [regex]::Replace($text, "(?m)^\s*-\s+name:\s+Upload telemetry artifacts", ($blockStatePolicy + "`n      - name: Upload telemetry artifacts"), 1)
    Ok "Inserted state/policy block before Upload telemetry artifacts."
  } else {
    Warn "Upload telemetry artifacts step not found; skipping state/policy insertion."
  }
} else {
  Ok "State/policy block already present; skipping."
}

# Insert proposal block after "Validate control decision schema" step
if (-not (Contains $text "Enforce policy gate (Es->Lambda->T)")) {
  $lines2 = $text -split "`n"
  $out = New-Object System.Collections.Generic.List[string]
  $inserted = $false
  for ($i=0; $i -lt $lines2.Count; $i++) {
    $out.Add($lines2[$i])
    if (-not $inserted -and $lines2[$i] -match "^\s*-\s+name:\s+Validate control decision schema\s*$") {
      $i++
      while ($i -lt $lines2.Count) {
        $out.Add($lines2[$i])
        if ($lines2[$i].Trim() -eq "") { break }
        $i++
      }
      foreach ($l in ($blockProposal -split "`r?`n")) { $out.Add($l) }
      $inserted = $true
    }
  }
  $text = ($out -join "`n")
  if ($inserted) { Ok "Inserted proposal block after Validate control decision schema." }
  else { Warn "Validate control decision schema step not found; skipping proposal insertion." }
} else {
  Ok "Proposal block already present; skipping."
}

# Write back
$text | Out-File -FilePath $WorkflowPath -Encoding UTF8

Ok "CI workflow patched successfully."
Say "File: $WorkflowPath"
Say "Backup: $backup"
Say "Tip: run 'git diff .github/workflows/ci.yml' to review changes."
