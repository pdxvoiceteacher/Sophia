# v3 Kernel: Three-Plane Architecture and Hardening Summary

Kernel (Thomas) = lawful PDE engine: compiler + engine with typed AST, operator registry, and rich `FieldSpec` registry. It implements deterministic integration, phase transitions, and governance.

Consent Layer (Joe) = PatternDonation interface: narrative/acoustic artifacts with explicit consent metadata. All pattern donations are advisory only, subject to compile-time checks and no direct mutation of derived/governance fields.

Audit/Overlay Plane (Sophia/Atlas): telemetry and audit outputs, watch/docket records, hashed state snapshots, and reset-safe visual overlays.

This braid realizes a deterministic coherence-field compiler under strict ethics: Joe’s rules become admissibility constraints; Thomas’s math becomes the executable substrate; and the system logs an auditable trail rather than opaque control.

## 1. Field Registry as Constitutional Core

- `FieldSpec` (new dataclass) holds `name`, `role`, `locality`, `bounds`, `governanceClass`, `shape`, `derived_from`, `dtype`, `conserved`, `writable`, etc.
- Enforces at compile-time: derived fields are immutable, locality rules, and bounded ranges.
- Allows per-field projection rules (clip, reflect, no-saturation for specified fields).
- Example:

```python
from dataclasses import dataclass
from typing import Literal, Optional, Tuple

@dataclass(frozen=True)
class FieldSpec:
    name: str
    role: Literal["primitive", "derived", "observable"]
    locality: Literal["node", "edge", "global"]
    bounds: Tuple[Optional[float], Optional[float]] = (0.0, 1.0)
    governance: str  # e.g. "open", "sensitive"
    shape: Literal["scalar", "vector", "tensor"] = "scalar"
    conserved: bool = False
    derived_from: Tuple[str, ...] = ()
    writable: bool = True
    dtype: Literal["float", "bool", "int", "complex"] = "float"
```

- `OperatorSpec` (refined) is typed and includes inputs, outputs, params, apply function, etc., so the compiler knows each operator signature explicitly.

## 2. Typed AST and Operator Registry

- AST nodes (e.g. `FieldExpr`, `ConstExpr`, `AddExpr`, etc.) remain pure algebraic (no graph ops). Complex ops like Laplacian or divergence stay in operator implementations.
- Example AST class:

```python
from dataclasses import dataclass

@dataclass(frozen=True)
class Expr:
    pass

@dataclass(frozen=True)
class FieldExpr(Expr):
    field: str

    def eval(self, state):
        return state[self.field]
```

- `OperatorRegistry` maps operator names to implementations.
- For each operator (diffusion, advection, source, sink, etc.), store an `OperatorSpec`.
- Operators return `FieldContribution` records instead of mutating state directly:

```python
from dataclasses import dataclass

@dataclass(frozen=True)
class FieldContribution:
    field: str
    locality: str
    value: float
```

- During execution, contributions are validated against the `FieldRegistry` before aggregation.

## 3. Compiler Pipeline (Phase-aligned)

1. Parse JSON spec → AST: read unified spec schema (`operators` list) and build ASTs for derived-field formulas under pattern donations.
2. Normalize and validate.
3. Apply compile-time governance: reject unknown operators, disallowed derived targets, missing consent tags.
4. Ensure `FieldSpec` consistency (e.g., no operator writes a derived field).
5. Lower to operator graph plan: flatten AST into a list of operator calls with parameters.
6. Canonicalize and hash: normalize ordering (e.g., sort operators), compute hash of the plan for provenance tracking.

## 4. Evolution Engine and Integration

- Generic engine: a single `step_kernel(state, ops, dt)` method. Corridor, river, and terrace all use this base.
- Contribution aggregation: initialize empty `deltas: Dict[str, float]`. For each operator, call `contribs = op.apply(state, ...)` and merge into deltas (sum contributions). Validate each contribution’s field/locality.
- Integrate fields: for each primitive field `f`:

```python
new_val = state[f] + dt * deltas[f]
```

Then apply field-specific projection/bounds according to `FieldSpec`.

- Derived recompute: recompute all derived fields in topo-sorted order (`FieldSpec.derived_from`). Emit telemetry record `DerivedRecompute` when needed.
- Governance projection: after integration, apply governance rules. If a predicted jump violates policy, clip, queue review, or downgrade to advisory (separate from numeric projection).

## 5. New First-Class Artifacts

- `PhaseTransitionWitness`: emitted when crossing regime boundaries. Contains `fromPhase`, `toPhase`, `targetId`, `triggerMetrics`, `kernelHash`, `supportingArtifacts`, and `advisoryNote`. Provides explainable causality for shifts (corridor→river, river→terrace, etc.).
- `RuntimeControlState`: captures operator-user feedback (`abort`, `downgradeToAdvisory`, `requireHumanReview`).
  - Hard abort flag stops execution immediately.
  - `downgradeToAdvisory` disables scheduled ops.
  - `requireHumanReview` pauses execution.
  - Settable via UI/API to satisfy explicit human control rights.

## 6. Execution Profiles and Modes

- Define profiles (`lean_safe`, `runtime_graph`, `research_field`, `experimental`) restricting operators/fields.
- Example: `research_field` may allow fixed-seed stochastic novelty injections; `lean_safe` forbids randomness.
- Every run specifies a profile; compiler enforces it.

## 7. Deposit-Only Pattern Donations

- `PatternDonationSpec` (advisory-only): incoming artifact with `donation_id`, `level`, `modality`, `content_ref`, `intended_targets`, `provenance`, `consent`, `audit_tags`, `artifact_mode`.
- Processing:
  - Compiler validates donation against active profile and consent level.
  - Donation hints may map to parameters only if admissible.
  - Unapproved donations are logged as advisories.
- Donations never directly write state or override derived fields; they route through the same compiled operator pipeline.

## 8. Audit and Public Overlays

- Telemetry stream (TEL): each step emits core metrics (`kernelHash`, `ΔΨ`, `ΔS` spikes, field summaries, control flags) for dashboards.
- Sophia audit:
  - Emits JSONL with severity (`info`, `warn`, `docket`, `watch`) for governance events.
  - Validates records against schema.
  - Uses deterministic serialization (`sort_keys=True`) for reproducibility.
  - Includes context (which field/operator triggered block).
  - Advisory messages remain watch/docket, never elevated as authoritative errors.
- Atlas overlays:
  - Load state from canonical artifacts (not global vars).
  - Keep toggles idempotent and centrally clear CSS classes.
  - `clearNavigationOverlay` performs full reset.
  - Overlay visualizes observable fields only (not protected underlying internals).

## 9. Repair/Rebraiding Test Harness

- Add scenario fixtures in `tests/repair/` named after Joseph arcs (`hidden_to_exposed.json`, `reconciliation_arc.json`, etc.).
- Each fixture defines a state evolution/donation sequence expected to reach known outcomes.
- Validate higher-order invariants, e.g. after rebraid donation:
  - `shared_memory_overlap` increases.
  - `trust_legibility_overlap` remains nonzero.

## 10. Remaining Hardening / Merge Gates

Before declaring this kernel final (terrace), ensure:

- FieldSpec completeness: all fields (including social fields like `status_asymmetry`, `shared_memory_overlap`, `translation_capacity`, `trust_legibility`) are declared.
- Derived DAG surfaced: emit derived-field computation as explicit phase with telemetry.
- Projection vs governance outputs are separated in audit logs.
- Corridor and river share one engine (`step_kernel`) rather than duplicated updaters.
- Golden-path CI: compile → step → telemetry → audit → overlay passes end-to-end.
- Explainability: no single authoritative truth voice; all outputs are labeled non-authoritative and include source hashes.

---

## Closing Position

Developer Echo v2 hardening remains the core. This architecture is a two-layer, three-plane braid:

- Thomas layer (engine): enforces triadic-brain laws (phase transitions, braid invariants).
- Joe layer (consent overlay): enforces ethics (admissibility constraints, consent metadata, human control).
- Audit layer: ensures full traceability (telemetry logs, clean overlays).

That braid makes the PDE compiler the execution nucleus (not a sidecar), with symbolic extensions explicitly bounded by governance. Advanced pattern donations become testable suggestions with no stealth authority.

The two most novel additions are `PhaseTransitionWitness` and `RuntimeControlState`, making each phase shift and each abort/downgrade explicit and auditable. With these and the hardening checklist satisfied, this design reaches terrace-grade governance and traceability.
