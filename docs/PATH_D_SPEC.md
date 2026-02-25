# PATH D — Cognition Trace (D2)

## D2 Contract: Hardening

Path D cognition traces are **producer-only**, **out-of-band** metadata and are not part of Secure Swarm consensus or governance state.

### Isolation guarantees

- `cognition_trace.json` is emitted separately from consensus and attestation artifacts.
- Consumer ingest is expected to ignore cognition artifacts by design.
- Cognition traces are **not** part of consensus gates.

### Determinism guarantees

- Trace payload is schema-bound (`schema/cognition_trace_v1.schema.json`).
- Serialization uses sorted keys.
- List sections are stably sorted before write.
- No timestamps, UUIDs, random fields, or runtime entropy are included.

### Non-impact guarantees

Enabling cognition reflection mode must not change bytes of:

- `consensus_summary.json`
- `evidence_bundle.json`
- `attestations.json`
- `peer_attestations.json`

Path A/B/C invariants remain unchanged.


## D3 Contract: Persistent deterministic memory graph

- `cognition_memory_graph.json` is producer-only and out-of-band.
- Graph updates are deterministic and idempotent for identical traces.
- Memory graph is not included in Secure Swarm consensus gates.
- Memory graph updates must not change bytes of:
  - `consensus_summary.json`
  - `evidence_bundle.json`
  - `attestations.json`
  - `peer_attestations.json`
