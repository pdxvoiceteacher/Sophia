# Path B1 Acceptance Criteria

Path B1 changes are eligible only when all criteria below are satisfied.

## Required gates
- [ ] Path A invariant suite passes (`tests/test_path_a_freeze_invariants.py`).
- [ ] All existing focused governance tests pass.
- [ ] Deterministic freeze verifier is green on witness-only path.

## Contract integrity
- [ ] `consensus_summary_v1` emission is unchanged for `witness_only`.
- [ ] `consensus_summary_v2` emission is isolated to weighted profiles (`reproducible_audit`, `full_relay`).
- [ ] No Path B metadata appears in v1 witness output.

## Consensus safety
- [ ] Central dominance preserved (no convergence when central is non-pass).
- [ ] Weighted math behavior matches `docs/PATH_B1_WEIGHTED_CONSENSUS_SPEC.md`.
- [ ] Drift/adversarial simulation tests pass and are deterministic with pinned replay inputs.

## Documentation completeness
- [ ] Path B1 weighted consensus math spec documented.
- [ ] Path B scope vs Path A freeze scope documented clearly.
- [ ] Non-goals (registry/governance shifts) explicitly deferred to Path B2+.
