# PATH D — Cognition (D1–D5)

## D1 Contract: Out-of-band cognition baseline

- Cognition artifacts are producer-only outputs and are **never** governance inputs.
- Cognition artifacts must not be added to `evidence_bundle.json` artifact lists.
- Cognition code paths are optional and default-off.

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
- D4 cognition graph+recall emission is gated and only allowed when all of the following are true:
  - weighted profile (`reproducible_audit` or `full_relay`)
  - structured reflection mode enabled
  - `--cognitive-memory-graph-mode update`
  - `--cognitive-memory-graph-path` is set
  - `--cognitive-memory-recall-mode emit`
  - `--cognitive-memory-recall-path` is set
- If any gate is missing, no cognition trace/graph/recall artifacts are written by this D4 path.
- Cognition artifacts remain out-of-band and are not included in `evidence_bundle.json` artifact entries.

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


## D5 Contract: Persistent deterministic memory hardening

- Determinism for memory graph updates is defined as: **given the same prior graph bytes and the same cognition trace payload, output graph bytes are identical**.
- Optional bounded-memory pruning is available only through explicit knobs:
  - `--cognitive-memory-max-nodes N`
  - `--cognitive-memory-max-edges M`
  - `0` keeps pruning disabled (default).
- Pruning applies only during the memory graph update step and is deterministic:
  - node pruning removes lowest-degree nodes first, then lexicographic `node_id` tie-breaker
  - edge pruning uses lexicographic `edge_id` ordering
- Corrupt or partial graph files are recovered deterministically by treating input as empty graph and rewriting valid schema-bound output.
- D5 remains out-of-band and must not change bytes of governance artifacts:
  - `consensus_summary.json`
  - `evidence_bundle.json`
  - `attestations.json`
  - `peer_attestations.json`

Path A/B/C governance logic, bundle hashing, replay ledger behavior, and trust enforcement remain unchanged.


## Path E Contract: Deterministic cognition task plan (out-of-band)

- `cognition_task_plan.json` is producer-only, deterministic, and out-of-band.
- Path E emission is strict AND-gated and requires all Path D gates plus:
  - `--cognitive-task-plan-mode emit`
  - `--cognitive-task-plan-path` is set
- If any gate is missing, no cognition artifacts are written (`cognition_trace.json`, `cognition_memory_graph.json`, `cognition_memory_recall.json`, `cognition_task_plan.json`).
- Determinism definition: given the same prior graph bytes, same trace payload, and same recall payload, task-plan bytes are identical.
- Task plan stays out of governance and must not change bytes of:
  - `consensus_summary.json`
  - `evidence_bundle.json`
  - `attestations.json`
  - `peer_attestations.json`
- `cognition_task_plan.json` must not be added to `evidence_bundle.json` artifacts list.
