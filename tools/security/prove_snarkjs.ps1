param(
  [Parameter(Mandatory=$true)][string]$VoteDir,
  [string]$ProverManifest = "prover_manifest.json",
  [string]$SnarkjsBin = $env:UCC_SNARKJS_BIN,
  [string]$PythonExe = $env:UCC_PYTHON_EXE
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

if (-not $SnarkjsBin) { $SnarkjsBin = "snarkjs" }
if (-not $PythonExe)  { $PythonExe  = "python" }

$VoteDir = (Resolve-Path $VoteDir).Path

function Get-Full([string]$p) {
  if (-not $p) { return $null }
  if ([System.IO.Path]::IsPathRooted($p)) { return [System.IO.Path]::GetFullPath($p) }
  return [System.IO.Path]::GetFullPath((Join-Path $VoteDir $p))
}

function Assert-InsideVoteDir([string]$fullPath, [string]$label) {
  $root = [System.IO.Path]::GetFullPath($VoteDir)
  if (-not $root.EndsWith([System.IO.Path]::DirectorySeparatorChar)) {
    $root = $root + [System.IO.Path]::DirectorySeparatorChar
  }
  $fp = [System.IO.Path]::GetFullPath($fullPath)
  if (-not $fp.StartsWith($root, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "$label must remain inside vote_dir. Got: $fp"
  }
}

# --- Load vote_manifest.json (required for strict public.deliberation) ---
$vmPath = Join-Path $VoteDir "vote_manifest.json"
if (-not (Test-Path $vmPath)) { throw "Missing vote manifest: $vmPath" }
$vm = Get-Content $vmPath -Raw | ConvertFrom-Json

$scope = $null
if ($vm.purpose -and $vm.purpose.scope) { $scope = [string]$vm.purpose.scope }
$policyVerifier = $null
$policyCircuit  = $null
if ($vm.proof_policy) {
  if ($vm.proof_policy.verifier_id) { $policyVerifier = [string]$vm.proof_policy.verifier_id }
  if ($vm.proof_policy.circuit_id)  { $policyCircuit  = [string]$vm.proof_policy.circuit_id }
}

# --- Load prover_manifest.json ---
$pmPath = Join-Path $VoteDir $ProverManifest
if (-not (Test-Path $pmPath)) { throw "Missing prover manifest: $pmPath" }
$pm = Get-Content $pmPath -Raw | ConvertFrom-Json

# Validate prover manifest schema (fast fail before running snarkjs)
$validator = Join-Path (Resolve-Path .).Path "tools\security\validate_prover_manifest.py"
if (Test-Path $validator) {
  & $PythonExe $validator --manifest $pmPath | Out-Null
}

$pmVerifier = if ($pm.verifier_id) { [string]$pm.verifier_id } else { "" }
$pmCircuit  = if ($pm.circuit_id)  { [string]$pm.circuit_id }  else { "" }

$pmStrict = $false
if ($pm.public_inputs -and ($pm.public_inputs.strict -is [bool])) { $pmStrict = [bool]$pm.public_inputs.strict }

$isPublicStrict = ($pmStrict -and ($scope -eq "public.deliberation"))

# v2.7 strict: enforce prover_manifest matches vote_manifest proof_policy
if ($isPublicStrict) {
  if (-not $policyVerifier -or -not $policyCircuit) {
    throw "Strict public.deliberation requires vote_manifest.proof_policy {verifier_id,circuit_id}"
  }
  if ($pmVerifier -ne $policyVerifier -or $pmCircuit -ne $policyCircuit) {
    throw "STRICT drift: prover_manifest(verifier_id,circuit_id)=($pmVerifier,$pmCircuit) must match vote_manifest.proof_policy=($policyVerifier,$policyCircuit)"
  }
}

# Resolve paths from prover manifest artifacts
$mode = [string]$pm.backend.mode
$alg  = ([string]$pm.backend.alg).ToUpper()

$vk     = Get-Full $pm.artifacts.vk_path
$wasm   = Get-Full $pm.artifacts.wasm_path
$zkey   = Get-Full $pm.artifacts.zkey_path
$input  = Get-Full $pm.artifacts.input_json_path
$wtns   = Get-Full $pm.artifacts.witness_path
$proof  = Get-Full $pm.artifacts.proof_json_path
$public = Get-Full $pm.artifacts.public_json_path

# v2.7 strict: refuse writing outside vote_dir
if ($isPublicStrict) {
  Assert-InsideVoteDir $vk     "vk_path"
  Assert-InsideVoteDir $proof  "proof_json_path"
  Assert-InsideVoteDir $public "public_json_path"
  if ($mode -eq "fullprover") {
    Assert-InsideVoteDir $input "input_json_path"
    Assert-InsideVoteDir $wasm  "wasm_path"
    Assert-InsideVoteDir $zkey  "zkey_path"
  } elseif ($mode -eq "prove") {
    Assert-InsideVoteDir $wtns  "witness_path"
    Assert-InsideVoteDir $zkey  "zkey_path"
  }
}

# Optional strict: check backend.alg matches verifier registry alg when we can
# (uses ucc/verifiers/registry.json OR overlay via UCC_VERIFIER_REGISTRY_PATH)
if ($isPublicStrict) {
  $regPath = $env:UCC_VERIFIER_REGISTRY_PATH
  if (-not $regPath) { $regPath = Join-Path $VoteDir "..\..\..\verifiers\registry.json" }  # best effort
  if (-not (Test-Path $regPath)) { $regPath = "ucc\verifiers\registry.json" }

  try {
    $reg = Get-Content $regPath -Raw | ConvertFrom-Json
    if ($reg.$pmVerifier -and $reg.$pmVerifier.alg) {
      $specAlg = ([string]$reg.$pmVerifier.alg).ToUpper()
      if ($specAlg -and $alg -and ($specAlg -ne $alg)) {
        throw "STRICT drift: prover_manifest.backend.alg=$alg must match verifier alg=$specAlg for $pmVerifier"
      }
    }
  } catch {
    # If registry can't be read, do not block proving (unless you want to make this fatal later)
  }
}

# Ensure output dirs exist
New-Item -ItemType Directory -Force -Path ([System.IO.Path]::GetDirectoryName($proof))  | Out-Null
New-Item -ItemType Directory -Force -Path ([System.IO.Path]::GetDirectoryName($public)) | Out-Null

# Run snarkjs
$algLower = $alg.ToLower()

if ($mode -eq "fullprover") {
  if (-not (Test-Path $input)) { throw "Missing input_json_path: $input" }
  if (-not (Test-Path $wasm))  { throw "Missing wasm_path: $wasm" }
  if (-not (Test-Path $zkey))  { throw "Missing zkey_path: $zkey" }
  & $SnarkjsBin $algLower fullprover $input $wasm $zkey $proof $public
}
elseif ($mode -eq "prove") {
  if (-not (Test-Path $wtns)) { throw "Missing witness_path: $wtns" }
  if (-not (Test-Path $zkey)) { throw "Missing zkey_path: $zkey" }
  & $SnarkjsBin $algLower prove $zkey $wtns $proof $public
}
else {
  throw "Unsupported mode: $mode"
}

Write-Host "Wrote proof:  $proof"
Write-Host "Wrote public: $public"
