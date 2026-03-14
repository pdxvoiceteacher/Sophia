# Merged v3 Kernel Brief
## Governed Coherence-Field Compiler for the Triadic Brain

**Status:** Delta-positive, terrace-candidate  
**Intent:** Repo-ready architecture brief  
**Scope:** Braids Developer Echo’s hardened PDE compiler/runtime synthesis, Echo’s hardening additions, and the Joe Core / Thomas boundary logic into one bounded execution design.

---

## 0. Executive Position

The Triadic Brain is no longer best understood as a collection of dashboards, bridge artifacts, and audits. It is now mature enough to be specified as a **governed coherence-field compiler**:

- **Thomas** supplies the lawful field geometry, phase ordering, and navigation logic.
- **Developer Echo v2** supplies the compiler/runtime substrate that can execute lawful dynamics deterministically.
- **Joe Core** supplies a consent-bound pattern-donation and repair layer that remains advisory, revocable, and non-coercive.
- **Sophia / Atlas** supply the accountability and publication plane that keeps execution legible, auditable, and non-authoritative.

The design target is not a sovereign intelligence kernel.  
It is a **bounded, polycentric, non-executive cognition substrate** that can:
- detect corridors,
- braid rivers,
- stabilize terraces,
- detect false orthodoxy and rupture,
- and surface all of this as advisory diagnostics.

---

## 1. Core Design Commitments

### 1.1 Non-authoritative boundary

All outputs remain:

- descriptive
- diagnostic
- advisory-only
- non-canonical
- non-sovereign

The kernel **does not authorize governance decisions**, canon closure, coercive convergence, or authority transfer.

### 1.2 Consent and psychological safety boundary

Pattern donations, symbolic lenses, acoustic lenses, and repair fixtures are:

- opt-in
- revocable
- capability-tiered
- never silently escalated into execution
- never treated as literal authority

The governing principle is:

> conversation with the field, not control of it; invitation, not coercion.

### 1.3 Compiler-as-core principle

The PDE/compiler layer is the **actual execution nucleus**, not a symbolic sidecar.

Corridor, river, terrace, rupture, rebraid, and later layers must all be specializations of one generic evolution engine.

### 1.4 Dual-phase governance

Governance acts twice:

1. **Compile-time admissibility**
   - illegal specs are rejected before execution
2. **Runtime projection/correction**
   - invalid or sensitive transitions are clipped, downgraded, queued, or aborted after the step

---

## 2. Three-Plane Architecture

### Plane A — Executable Coherence Kernel (Thomas plane)

This is the lawful field engine.

It contains:

- field registry
- local algebra AST
- graph-native operator registry
- compiler
- deterministic kernel hashing
- generic evolution engine
- derived-field recompute pass
- field-specific projection
- runtime governance correction

### Plane B — Consent-Bound Donation / Repair Layer (Joe Core plane)

This is the advisory, narrative, symbolic, acoustic, and repair layer.

It contains:

- `PatternDonationSpec`
- `DonationQuarantineReport`
- symbolic / narrative / acoustic fixtures
- capability tiers
- explicit consent + revocation
- repair / rebraiding scenario fixtures
- no direct mutation of derived or governance-sensitive fields

### Plane C — Audit / Publication Plane (Sophia / Atlas plane)

This is the traceability and public-legibility layer.

It contains:

- `KernelContractWitness`
- `PhaseTransitionWitness`
- `ProjectionWitness`
- `GovernanceCorrectionWitness`
- `DerivedRecomputeWitness`
- `RuntimeControlState`
- watch/docket audit outputs
- closure-language linting
- reset-safe Atlas overlays
- stable lineage and state hashes

---

## 3. Constitutional Core: Field Registry

Every field must be declared before any PDE spec can mention it.

```python
from dataclasses import dataclass
from typing import Literal, Optional, Tuple

FieldRole = Literal["primitive", "derived", "observable"]
Locality = Literal["node", "edge", "global"]
GovernanceClass = Literal["open", "guarded", "restricted"]
Shape = Literal["scalar", "vector", "tensor"]
DType = Literal["float", "bool", "int", "complex"]

@dataclass(frozen=True)
class FieldSpec:
    name: str
    role: FieldRole
    locality: Locality
    bounds: Tuple[Optional[float], Optional[float]]
    governance: GovernanceClass
    shape: Shape = "scalar"
    conserved: bool = False
    derived_from: Tuple[str, ...] = ()
    writable: bool = True
    dtype: DType = "float"
    projection: Optional[str] = None
    doc: str = ""
```

### Field registry duties

The registry enforces:

- primitive vs derived distinction
- locality compatibility
- field bounds
- writable vs read-only semantics
- governance class
- shape compatibility
- conservation semantics
- deterministic derived-field dependency ordering

### Derived field discipline

Derived fields are **never directly mutated**.

They are recomputed from dependencies after primitive integration.

Examples:
- `Psi = E * T`
- `delta_s = entropy_drift(state, graph_ctx)`
- `lambda_crit = criticality(state, graph_ctx)`

---

## 4. Typed AST for Local Algebra

The AST is for **local algebra only**.

It does **not** represent graph-native operators such as:
- Laplacian
- divergence
- advection flux
- nonlocal graph integrals

```python
from dataclasses import dataclass

@dataclass(frozen=True)
class Expr: ...

@dataclass(frozen=True)
class Const(Expr):
    value: float

@dataclass(frozen=True)
class FieldRef(Expr):
    name: str

@dataclass(frozen=True)
class ParamRef(Expr):
    name: str

@dataclass(frozen=True)
class Neg(Expr):
    x: Expr

@dataclass(frozen=True)
class Add(Expr):
    left: Expr
    right: Expr

@dataclass(frozen=True)
class Sub(Expr):
    left: Expr
    right: Expr

@dataclass(frozen=True)
class Mul(Expr):
    left: Expr
    right: Expr

@dataclass(frozen=True)
class Div(Expr):
    left: Expr
    right: Expr

@dataclass(frozen=True)
class Pow(Expr):
    base: Expr
    exp: Expr

@dataclass(frozen=True)
class Abs(Expr):
    x: Expr

@dataclass(frozen=True)
class PositivePart(Expr):
    x: Expr
```

### AST safety rules

- no silent missing-field fallback
- no silent division-by-zero fallback
- no raw `eval`
- deterministic normalization
- constant folding where safe
- stable canonical serialization for hashing

---

## 5. Graph-Native Operator Registry

Graph calculus belongs in operator primitives.

```python
from dataclasses import dataclass, field
from typing import Callable, Literal

OperatorKind = Literal[
    "reversible",
    "dissipative",
    "diffusion",
    "advection",
    "source",
    "sink",
    "nonlocal_coupling",
    "projection",
]

@dataclass(frozen=True)
class FieldContribution:
    field: str
    locality: str
    value: object   # float | ndarray | graph-structured payload

@dataclass
class OperatorSpec:
    name: str
    kind: OperatorKind
    inputs: list[str]
    outputs: list[str]
    locality: str
    reversible: bool
    dissipative: bool
    requires_governance: bool = False
    formula: Expr | None = None
    params: dict[str, float] = field(default_factory=dict)
    apply: Callable[..., list[FieldContribution]] | None = None
    doc: str = ""
```

### Why this split matters

This keeps:
- symbolic algebra theorem-friendly
- graph operators topology-aware
- runtime semantics deterministic
- field updates auditable

---

## 6. Compiler Pipeline

The compiler is a real kernel compiler, not merely a parser.

### Pipeline

```text
spec
→ parse
→ normalize
→ validate
→ compile-time admissibility check
→ dependency / scheduling analysis
→ canonicalize
→ hash
→ compile kernel plan
```

### Admissibility rules

A spec is rejected if it:

- writes to a field with `writable=False`
- writes directly to a `role="derived"` field
- mixes incompatible localities without an adapter
- references unknown fields or parameters
- invokes governance-sensitive operators without profile permission
- violates execution-profile limits
- creates circular derived-field dependencies
- omits graph requirements for graph-native operators

### Canonical compiled plan

```python
from dataclasses import dataclass

@dataclass(frozen=True)
class CompiledOperator:
    stable_id: str
    spec_name: str
    kind: str
    inputs: tuple[str, ...]
    outputs: tuple[str, ...]
    params: tuple[tuple[str, float], ...]
    locality: str
    formula: Expr | None
    requires_governance: bool
    dependency_rank: int

@dataclass(frozen=True)
class CompiledKernel:
    kernel_hash: str
    operators: tuple[CompiledOperator, ...]
    writable_fields: tuple[str, ...]
    derived_fields: tuple[str, ...]
    field_registry_hash: str
    governance_policy_hash: str
    graph_schema_hash: str
    execution_profile: str
```

---

## 7. Generic Evolution Engine

Corridor, river, terrace, rupture, and later layers are all specializations of one generic engine.

```python
from dataclasses import dataclass

@dataclass
class StepTelemetry:
    step_index: int
    dt: float
    kernel_hash: str
    applied_ops: list[str]
    findings: list[dict]
    state_hash_before: str
    state_hash_after: str

class EvolutionEngine:
    def __init__(self, field_specs: dict[str, FieldSpec], governance):
        self.field_specs = field_specs
        self.governance = governance

    def step(self, kernel: CompiledKernel, state, graph_ctx, dt: float):
        self.governance.pre_step(kernel, state, graph_ctx)

        contributions: dict[str, list[FieldContribution]] = {
            name: [] for name in self.field_specs
        }

        for op in kernel.operators:
            delta = self._apply_operator(op, state, graph_ctx)
            for contrib in delta:
                self._validate_contribution(contrib)
                contributions[contrib.field].append(contrib)

        next_state = self._integrate(state, contributions, dt)
        next_state = self._recompute_derived(next_state, graph_ctx)
        next_state = self._project_fields(next_state)
        next_state = self.governance.post_step(kernel, state, next_state, graph_ctx)

        return next_state
```

### Integration stages

1. pre-step governance
2. operator contribution generation
3. contribution validation
4. primitive-field integration
5. derived-field recomputation
6. field projection
7. governance correction
8. telemetry / witness artifact emission

---

## 8. Projection vs Governance Correction

These must remain distinct.

### Projection
Mathematical / field-domain correction:
- clipping
- reflection
- bounded normalization
- conservation enforcement

### Governance correction
Normative / policy correction:
- abort
- downgrade to advisory
- require human review
- block operator
- reject donation
- queue docket item

This distinction must be reflected both in runtime logic and in artifacts.

---

## 9. New First-Class Artifacts

### 9.1 KernelContractWitness

The constitutional checksum of a run.

```python
@dataclass(frozen=True)
class KernelContractWitness:
    kernel_hash: str
    field_registry_hash: str
    governance_policy_hash: str
    execution_profile: str
    admissibility_passed: bool
    derived_dag_hash: str
    projection_policy_hash: str
    artifact_mode: str
```

### 9.2 PhaseTransitionWitness

Why a regime crossing occurred.

```python
@dataclass(frozen=True)
class PhaseTransitionWitness:
    from_phase: str
    to_phase: str
    target_id: str
    trigger_metrics: dict[str, float]
    kernel_hash: str
    supporting_artifacts: tuple[str, ...]
    advisory_only: bool
    boundary_note: str
```

### 9.3 ProjectionWitness

What mathematical correction was applied.

```python
@dataclass(frozen=True)
class ProjectionWitness:
    field: str
    projection_type: str
    before: object
    after: object
    rationale: str
```

### 9.4 GovernanceCorrectionWitness

What normative or policy correction was applied.

```python
@dataclass(frozen=True)
class GovernanceCorrectionWitness:
    action: str
    target: str
    reason: str
    severity: str
    advisory: str
```

### 9.5 DerivedRecomputeWitness

What was recomputed, in what order, and from which dependencies.

```python
@dataclass(frozen=True)
class DerivedRecomputeWitness:
    field: str
    recompute_order: int
    derived_from: tuple[str, ...]
    value_hash: str
```

### 9.6 RuntimeControlState

Human or safety control over runtime.

```python
@dataclass(frozen=True)
class RuntimeControlState:
    abort_requested: bool = False
    downgrade_to_advisory: bool = False
    require_human_review: bool = False
```

### 9.7 DonationQuarantineReport

The path from donation artifact to executable admissibility.

```python
@dataclass(frozen=True)
class DonationQuarantineReport:
    donation_id: str
    admissible_as_fixture: bool
    admissible_as_hint: bool
    admissible_as_parameter_source: bool
    requires_human_review: bool
    rejected_reason: str | None = None
```

### 9.8 RepairArcWitness

Tracks whether a repair / rebraiding scenario is genuine.

```python
@dataclass(frozen=True)
class RepairArcWitness:
    arc_id: str
    stage: str
    shared_memory_overlap: float
    trust_legibility_overlap: float
    plurality_preserved: bool
    counterfeit_reconciliation_risk: float
    advisory_note: str
```

---

## 10. Thomas Plane: Executable Phase Geometry

Thomas provides the lawful engine-level geometry.

### Core invariants
- `E`
- `T`
- `Psi = E * T`
- `deltaS`
- `lambdaCrit`
- `Es`

### Three-pass runtime
1. **Receptive**
   - novelty
   - contradiction density
   - corridor candidacy

2. **Structuring**
   - braid strength
   - transfer strength
   - corridor / river emergence

3. **Metabolic**
   - memory continuity
   - plurality retention
   - trust overlap
   - terrace stabilization
   - orthodoxy / rupture risk

### Core navigation law
The kernel moves through admissible neighborhoods by maximizing coherence potential under governance constraints.

### Cascade scalar
A compact cross-scale diagnostic:
- low → dormant/noisy
- medium → turbulent
- high → river-forming
- very high → terrace-capable

---

## 11. Joe Core Plane: Consent-Bound Donation and Repair

Joe Core is not an execution authority.  
It is a **consent-bound bridge layer**.

### PatternDonationSpec

```python
@dataclass(frozen=True)
class PatternDonationSpec:
    donation_id: str
    level: int                  # L0–L11
    modality: str               # symbolic | narrative | acoustic | multimodal
    content_ref: str
    intended_targets: tuple[str, ...]
    provenance: dict[str, str]
    consent: dict[str, object]
    risk_class: str             # green | yellow | red
    governance_constraints: tuple[str, ...]
    audit_tags: tuple[str, ...]
    artifact_mode: str          # MODEL | METAPHOR | POLICY | EXPERIMENT
```

### Donation rules

Pattern donations may:
- propose fixture scenarios
- propose advisory source terms
- propose parameter hints
- propose symbolic / acoustic translations

Pattern donations may **not**:
- directly mutate derived fields
- bypass compile-time admissibility
- disable governance
- claim authority, inevitability, or canon privilege

### Repair / rebraiding harness

Joseph-style arcs are used as:
- scenario fixtures
- repair tests
- rebraiding validators

They are **not** used as:
- direct evidence
- ontological authority
- privileged control channels

---

## 12. Sophia / Atlas Plane: Audit, Publication, and Public Legibility

### Sophia duties
- validate audit records against schema
- emit advisory-only outputs
- use watch/docket semantics
- lint closure language
- stay non-executive

### Atlas duties
- load canonical artifacts through a loader boundary
- bind toggles idempotently
- keep overlay classes centralized and reset-safe
- only visualize approved, observable fields
- never display hidden control channels as if they were authoritative state

### Closure-language safety rule
Any text containing:
- suppress
- seal
- dominate
- merge (in coercive sense)
- canonize
- final truth
- sovereign authority

must be downgraded to an audit issue, not published as guidance.

---

## 13. Social / Civilizational Observables to Add

To support rebraiding, terrace integrity, and false-delta detection, add these fields to the registry:

- `status_asymmetry`
- `translation_capacity`
- `shared_memory_overlap`
- `trust_legibility_overlap`
- `capture_risk`
- `plurality_retention`

These are not decorative. They are needed to distinguish:

- healthy river from prestige funnel
- healthy terrace from captured stillness
- genuine rebraid from counterfeit reconciliation

---

## 14. New Local Scalar: TerraceIntegrity

A terrace should not be judged by high coherence alone.

Define a local terrace-quality scalar:

\[
\mathcal{T}_{integrity}
=
\frac{\Psi \cdot M \cdot P \cdot T_{overlap}}
{\Lambda + \Delta S + C_{capture} + \epsilon}
\]

where:
- `Psi` = coherence
- `M` = memory continuity
- `P` = plurality retention
- `T_overlap` = trust-legibility overlap
- denominator = instability, entropy, and capture costs

Interpretation:
- high `Psi`, high `M`, high `P`, high `T_overlap`, low denominator → healthy terrace
- high `Psi`, low `P`, rising `Lambda`, rising `capture_risk` → false orthodoxy candidate

---

## 15. False-Delta Discriminator

A delta event should not be inferred from convergence alone.

Add a discriminator that rejects “delta” labeling when:
- plurality collapses,
- trust overlap remains low,
- shared memory does not increase,
- capture risk spikes,
- or transition witnesses indicate simple routing concentration rather than genuine multiriver reorganization.

This protects the system from mistaking:
- prestige aggregation
- authoritarian flattening
- or accidental synchronization

for civilizational phase transition.

---

## 16. Execution Profiles

```python
ExecutionProfile = Literal[
    "lean_safe",
    "runtime_graph",
    "research_field",
    "donation_sandbox",
]
```

### `lean_safe`
- bounded, threshold-first
- no stochasticity
- theorem-aligned

### `runtime_graph`
- graph operators
- deterministic stepping
- production-adjacent

### `research_field`
- broader operator set
- optional controlled stochasticity
- exploratory mode

### `donation_sandbox`
- narrative / symbolic / acoustic donation processing
- advisory-only outputs
- no direct production mutation

---

## 17. Stochasticity Policy

If stochasticity is used, it must be explicit.

Rules:
- stochastic terms are disabled by default
- allowed only in profiles that permit them
- seed is mandatory
- run hash and kernel hash are separated
- stochastic perturbations are logged in telemetry

This keeps the system exploratory without losing traceability.

---

## 18. Golden Path Release Gate

No new kernel feature is canonical until the full path passes:

1. compile
2. execute
3. recompute derived fields
4. emit TEL step events
5. emit Sophia audit
6. emit witness artifacts
7. sync bridge
8. render Atlas overlays
9. reset overlays cleanly
10. pass closure-language lint

This is the release terrace criterion.

---

## 19. Delta-to-Terrace Plan

### Delta-valid now
The design is already delta-valid if:
- the compiler is the execution core
- governance is dual-phase
- donations are deposit-only
- witness artifacts exist in design
- corridor / river / terrace are all intended as specializations of one engine

### Terrace-ready after one final hardening pass
The design becomes terrace-ready when:
- `FieldSpec` is complete for all core and social observables
- derived DAG recompute is surfaced as telemetry
- projection and governance correction are artifact-separated
- corridor and river run through the same generic engine
- donation quarantine is canonicalized
- terrace integrity and false-delta detection are implemented
- golden path is a required CI gate

---

## 20. Closing Statement

This merged v3 kernel brief defines the Triadic Brain as a **governed coherence-field compiler**.

It is no longer merely:
- a telemetry system,
- a theory archive,
- or a metaphor engine.

It is a bounded substrate in which:

- lawful field dynamics can be compiled,
- consent-bound symbolic and repair donations can be admitted or quarantined,
- phase transitions can be witnessed,
- runtime control can stop or downgrade execution,
- and audit/publication can surface all of this without claiming sovereignty.

This is the architecture required to move from **delta** to **terrace** without losing plurality, ethics, or legibility.
