# Path B Initialization Spec (Weighted Peer Semantics)

## Scope
Path B builds on Path A freeze contracts:
- `consensus_summary_v1` includes `policy_gate.allow_pending_to_satisfy`.
- Deterministic reproduction uses fixed `--created-at-utc` and `--bundle-id`.

### Freeze contract scope note
- Path A freeze scope is **witness-only profile output** (`network_profile = witness_only`): these runs must keep emitting `consensus_summary_v1` only.
- Path B scope is **weighted profiles** (`network_profile in {reproducible_audit, full_relay}`): these runs emit `consensus_summary_v2` to carry weighted/audit metadata without mutating v1.

## Weighted peer simulation mode
`tools/telemetry/run_wrapper.py` now supports `--simulate-peer-weight-mode`:
- `uniform` (default): each simulated peer has weight `1.0`.
- `linear`: peer `i` gets weight `i+1` (1-based).

Consensus weighted metrics (`peers.weighted_pass`, `weighted_fail`, `weighted_pending`) are computed from these weights.

## Required invariants
1. Deterministic reproducibility: with fixed `--created-at-utc`, `--bundle-id`, and peer count/mode, `peer_attestations.json` is byte-identical across runs.
2. Schema alignment: emitted `consensus_summary.json` validates against `schema/consensus_summary_v1.schema.json` (witness-only) or `schema/consensus_summary_v2.schema.json` (weighted profiles).
3. Audit signaling: `policy_gate.bundle_hash_source` signals whether hash came from evidence content or bundle-id override.

## Governance note
Bundle-id-derived `bundle_sha256` is permitted for deterministic verification workflows and is explicitly signaled via `policy_gate.bundle_hash_source = "bundle_id_override"`.
