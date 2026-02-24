#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

OUT_ROOT="${1:-out/release_gate_freeze}"
NETWORK_POLICY_PATH="config/network_policy_v1.json"
BACKUP_PATH="$(mktemp)"
RESTORE_MODE="none"

restore_policy() {
  if [[ "$RESTORE_MODE" == "restore" ]]; then
    cp "$BACKUP_PATH" "$NETWORK_POLICY_PATH"
  elif [[ "$RESTORE_MODE" == "remove" ]]; then
    rm -f "$NETWORK_POLICY_PATH"
  fi
  rm -f "$BACKUP_PATH"
}
trap restore_policy EXIT

if [[ -f "$NETWORK_POLICY_PATH" ]]; then
  cp "$NETWORK_POLICY_PATH" "$BACKUP_PATH"
  RESTORE_MODE="restore"
else
  RESTORE_MODE="remove"
fi

cat > "$NETWORK_POLICY_PATH" <<'JSON'
{
  "profile": "witness_only"
}
JSON

echo "[release_gate] running focused pytest governance gate"
python -m pytest -q \
  tests/test_path_a_freeze_invariants.py \
  tests/test_run_wrapper_evidence_paths.py \
  tests/test_secure_swarm_schemas.py \
  tests/test_epoch_real_runner.py \
  tests/test_run_wrapper_invocation.py

echo "[release_gate] running witness-only deterministic freeze verifier"
python scripts/verify_secure_swarm_freeze.py --repo-root . --out-root "$OUT_ROOT"

echo "[release_gate] PASS"
