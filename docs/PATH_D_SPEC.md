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


## D4 Contract: Deterministic cross-run memory recall

- `cognition_memory_recall.json` is producer-only and out-of-band.
- Recall reads `cognition_memory_graph.json` and emits a deterministic, schema-bound artifact (`schema/cognition_memory_recall_v1.schema.json`).
- Recall emission is gated and only allowed when all of the following are true:
  - weighted profile (`reproducible_audit` or `full_relay`)
  - structured reflection mode enabled
  - `--cognitive-memory-recall-mode emit`
  - `--cognitive-memory-recall-path` is set
- `--cognitive-memory-graph-path` must be set for recall because recall is derived from the graph file.

### Determinism and non-impact guarantees

- No timestamps, UUIDs, random fields, nonces, or runtime entropy are included.
- Recall serialization uses sorted keys and stable list ordering.
- Replaying the same run inputs yields byte-identical recall output.
- Recall remains outside governance paths and must not change bytes of:
  - `consensus_summary.json`
  - `evidence_bundle.json`
  - `attestations.json`
  - `peer_attestations.json`

Path A/B/C invariants and weighted consensus math remain unchanged.
