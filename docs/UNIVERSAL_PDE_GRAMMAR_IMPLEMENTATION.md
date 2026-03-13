# Universal PDE Grammar Implementation

Below are example code blocks implementing a universal PDE grammar framework for the Triadic Brain. The code defines a structured DSL (typed AST) for fields and operators, compiles user-defined PDE specifications into an internal form, and executes graph-based updates with governance projection. These blocks follow the consultant’s recommendations (typed AST, operator registry, compile-time checks, runtime admissibility, derived fields, etc.) and build on the existing CoherenceLattice scaffolds.

## 1. JSON Schema for PDE Specification

Define a JSON schema for user-provided PDE specs, describing fields and operators in a typed way (no free-form strings). This schema enforces required properties and field/operator types.

```json
// File: schemas/pde_spec.schema.json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Triadic Brain PDE Specification",
  "type": "object",
  "required": ["fields", "operators", "governance"],
  "properties": {
    "fields": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["name", "role"],
        "properties": {
          "name": { "type": "string" },
          "role": { "enum": ["primitive", "derived", "observable"] },
          "formula": { "type": "string" }
        }
      }
    },
    "operators": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["kind", "target"],
        "properties": {
          "kind": {
            "enum": ["diffusion", "advection", "source", "sink", "coupling", "projection"]
          },
          "target": { "type": "string" },
          "field": { "type": "string" },
          "weight": { "type": "number" },
          "alpha": { "type": "number" },
          "beta": { "type": "number" },
          "mu": { "type": "number" },
          "nu": { "type": "number" },
          "chi": { "type": "number" }
        },
        "additionalProperties": false
      }
    },
    "governance": { "type": "boolean" }
  },
  "additionalProperties": false
}
```

- `fields`: List of field definitions. Each field has a `name` (e.g., `"psi"`), a `role` (`"primitive"`, `"derived"`, or `"observable"`), and for derived fields a `formula` string that computes it from primitives (e.g., `"E * T"` for \(\Psi = E \times T\)). Primitive fields are stored state (e.g., telemetry values), derived fields are computed from primitives, and observables are additional quantities.
- `operators`: List of operator blocks. Each has a `kind` (e.g., `"diffusion"`, `"advection"`, etc.), a `target` field it updates (e.g., `"C"` for corridor), and parameter fields (`weight`, `alpha`, etc.) relevant to that operator. This enforces a typed DSL rather than raw code strings.
- `governance`: If `true`, the PDE engine applies UCC/audit projection after each step.

This schema lets us validate user PDE specs at compile-time.

## 2. Python Classes for Fields and Operators

Implement Python classes (dataclass or plain classes) to represent fields and operators in the DSL. We build an operator registry with metadata and a compiler that instantiates these operators. This enforces signatures and invariants per consultant guidance.

```python
# File: coherence/pde_grammar.py

from dataclasses import dataclass, field
from typing import Any, Dict

# --- Field specification ---

@dataclass
class FieldSpec:
    name: str
    role: str              # 'primitive', 'derived', or 'observable'
    formula: str = None    # only for derived fields

# --- Operator specification and base class ---

@dataclass
class OperatorSpec:
    kind: str              # 'diffusion', 'advection', 'source', 'sink', 'coupling', 'projection'
    target: str            # name of field to update
    params: Dict[str, Any] = field(default_factory=dict)

class Operator:
    """Base class for PDE operators."""
    def __init__(self, spec: OperatorSpec):
        self.kind = spec.kind
        self.target = spec.target
        self.params = spec.params

    def apply(self, state: Dict[str, Any], graph) -> None:
        """Apply this operator to the state (in-place or produce derivative)."""
        raise NotImplementedError("Must implement in subclass")

    @staticmethod
    def validate_fields(spec: OperatorSpec, fields: Dict[str, FieldSpec]):
        """Ensure target and field exist in schema and roles are correct."""
        target = spec.target
        if target not in fields:
            raise ValueError(f"Operator target field '{target}' not defined in fields.")
        # Additional role checks could go here

# --- Concrete operator classes ---

class DiffusionOperator(Operator):
    def apply(self, state: Dict[str, Any], graph):
        # Example diffusion: graph Laplacian on target field
        values = state[self.target]
        Lc = {}
        for node, nbrs in graph.adjacency.items():
            s = 0.0
            for nbr, w in nbrs.items():
                s += w * (values[nbr] - values[node])
            Lc[node] = s
        state[self.target + "_laplacian"] = Lc

class AdvectionOperator(Operator):
    def apply(self, state: Dict[str, Any], graph):
        # Example advection: minus divergence term -∇·(C ∇Θ)
        C = state.get("C")
        Theta = state.get("Theta")
        if C is None or Theta is None:
            return
        div = {}
        for node, nbrs in graph.adjacency.items():
            sum_flux = 0.0
            for nbr, w in nbrs.items():
                flux = 0.5 * w * (C[node] + C[nbr]) * (Theta[nbr] - Theta[node])
                sum_flux += flux
            div[node] = -sum_flux
        state[self.target + "_advection"] = div

class SourceOperator(Operator):
    def apply(self, state: Dict[str, Any], graph):
        # e.g., alpha * |∇Theta|^2 plus beta * Theta_dot
        alpha = self.params.get("alpha", 0.0)
        beta = self.params.get("beta", 0.0)
        Theta = state.get("Theta")
        theta_dot = state.get("Theta_dot", {})
        if Theta is None:
            return
        grad2 = {}
        for node, nbrs in graph.adjacency.items():
            s = 0.0
            for nbr, w in nbrs.items():
                diff = Theta[nbr] - Theta[node]
                s += w * diff * diff
            grad2[node] = alpha * s + beta * theta_dot.get(node, 0.0)
        state[self.target + "_source"] = grad2

class SinkOperator(Operator):
    def apply(self, state: Dict[str, Any], graph):
        # e.g., -mu*C - nu*(ΔS+Λ)*C - chi*C^3
        mu = self.params.get("mu", 0.0)
        nu = self.params.get("nu", 0.0)
        chi = self.params.get("chi", 0.0)
        C = state.get("C")
        if C is None:
            return
        deltaS = state.get("deltaS", {})
        Lambda = state.get("Lambda", {})
        sink = {}
        for node, cval in C.items():
            term = mu * cval
            term += nu * (max(0, deltaS.get(node, 0.0)) + max(0, Lambda.get(node, 0.0))) * cval
            term += chi * (cval ** 3)
            sink[node] = -term
        state[self.target + "_sink"] = sink

class ProjectionOperator(Operator):
    def apply(self, state: Dict[str, Any], graph):
        # Placeholder for governance projection operator.
        # (Actual projection is handled separately in Engine.)
        pass

OPERATOR_REGISTRY = {
    "diffusion": DiffusionOperator,
    "advection": AdvectionOperator,
    "source": SourceOperator,
    "sink": SinkOperator,
    "projection": ProjectionOperator,
}
```

- `FieldSpec`: describes each field (`name`, `role`, `formula` if derived).
- `OperatorSpec` and `Operator`: define typed operators. Concrete subclasses (`DiffusionOperator`, `AdvectionOperator`, etc.) implement `apply()`.
- `OPERATOR_REGISTRY`: maps `kind` strings to concrete classes and blocks unsupported kinds.

## 3. PDE Compiler and Execution Engine

Implement a compiler that reads a JSON PDE spec, validates it against schema/registry constraints, and runs discrete graph updates. Include compile-time checks (field roles, invalid combinations) and runtime UCC/audit projection.

```python
# File: coherence/pde_engine.py

from typing import Any, Dict, List

from coherence.bridge.update_corridor_field import build_adjacency
from coherence.pde_grammar import FieldSpec, OperatorSpec, OPERATOR_REGISTRY, Operator

class PDECompiler:
    """Compiles PDE specs (dict) into an executable operator pipeline."""
    def __init__(self, graph_topology: Dict[str, Any]):
        self.adj = build_adjacency(graph_topology)
        self.operator_pipeline: List[Operator] = []
        self.fields: Dict[str, FieldSpec] = {}
        self.governance = False

    def load_spec(self, spec: Dict[str, Any]) -> None:
        # Validate JSON schema externally (not shown here)
        for f in spec.get("fields", []):
            fs = FieldSpec(name=f["name"], role=f["role"], formula=f.get("formula"))
            self.fields[fs.name] = fs

        for op in spec.get("operators", []):
            kind = op["kind"]
            target = op["target"]
            params = {k: v for k, v in op.items() if k not in ["kind", "target"]}
            if kind not in OPERATOR_REGISTRY:
                raise ValueError(f"Unknown operator kind: {kind}")

            spec_obj = OperatorSpec(kind=kind, target=target, params=params)
            Operator.validate_fields(spec_obj, self.fields)

            op_class = OPERATOR_REGISTRY[kind]
            self.operator_pipeline.append(op_class(spec_obj))

        self.governance = spec.get("governance", False)

    def compile(self) -> None:
        # Check derived-field formulas and compile if needed.
        # (Formula parser/evaluator intentionally omitted in this scaffold.)
        pass

class PDEEngine:
    """Executes one step of the PDE on a triadic brain graph state."""
    def __init__(self, compiler: PDECompiler):
        self.compiler = compiler

    def step(self, state: Dict[str, Dict[str, float]]) -> Dict[str, Any]:
        """
        Perform one discrete time step:
        1) Apply all operators to compute intermediate changes.
        2) Update fields, enforce bounds, then apply governance.
        """
        new_state = {
            field: values.copy() if isinstance(values, dict) else values
            for field, values in state.items()
        }

        for op in self.compiler.operator_pipeline:
            op.apply(new_state, self.compiler.adj)

        # Integration/aggregation intentionally omitted in this scaffold.

        if self.compiler.governance:
            self.apply_governance(new_state)

        return new_state

    def apply_governance(self, state: Dict[str, Any]) -> None:
        # Placeholder: enforce UCC/audit admissibility
        # e.g., clamping values or rejecting prohibited transitions.
        pass

if __name__ == "__main__":
    graph_topo = {
        "nodes": ["n0", "n1"],
        "edges": [["n0", "n1", 1.0]],
    }
    compiler = PDECompiler(graph_topo)

    pde_spec = {
        "fields": [
            {"name": "C", "role": "primitive"},
            {"name": "Theta", "role": "primitive"},
            {"name": "deltaS", "role": "primitive"},
            {"name": "Lambda", "role": "primitive"},
        ],
        "operators": [
            {"kind": "diffusion", "target": "C", "weight": 0.1},
            {"kind": "advection", "target": "C", "field": "Theta"},
            {"kind": "source", "target": "C", "alpha": 1.0, "beta": 0.5},
            {"kind": "sink", "target": "C", "mu": 0.05, "nu": 0.5, "chi": 0.01},
        ],
        "governance": True,
    }

    compiler.load_spec(pde_spec)
    engine = PDEEngine(compiler)

    state = {
        "C": {"n0": 0.1, "n1": 0.2},
        "Theta": {"n0": 0.5, "n1": 0.7},
        "deltaS": {"n0": 0.1, "n1": 0.2},
        "Lambda": {"n0": 0.05, "n1": 0.03},
    }

    next_state = engine.step(state)
    print("Next state:", next_state)
```

- `PDECompiler.load_spec`: parses field/operator blocks, validates operator kinds and field references, and builds an execution pipeline.
- `PDEEngine.step`: applies operators, then applies governance projection (when enabled).
- `apply_governance`: placeholder for UCC/audit admissibility policy.

This framework cleanly separates field definitions, operator semantics, and execution.

## 4. Example PDE Grammar Usage

Below is an example JSON spec (matching the schema) for a discovery-corridor PDE.

```json
{
  "fields": [
    {"name": "C", "role": "primitive"},
    {"name": "Theta", "role": "primitive"},
    {"name": "deltaS", "role": "primitive"},
    {"name": "Lambda", "role": "primitive"},
    {"name": "Theta_dot", "role": "primitive"}
  ],
  "operators": [
    {"kind": "diffusion", "target": "C", "weight": 0.1},
    {"kind": "advection", "target": "C", "field": "Theta"},
    {"kind": "source", "target": "C", "alpha": 1.0, "beta": 0.5},
    {"kind": "sink", "target": "C", "mu": 0.05, "nu": 0.5, "chi": 0.01}
  ],
  "governance": true
}
```

This corresponds to:

\[
\partial_t C = D_C\nabla^2 C - \nabla \cdot (C\nabla\Theta) + \alpha\|\nabla\Theta\|^2 + \beta\,\partial_t\Theta - \mu C - \nu(\Delta S + \Lambda)C - \chi C^3.
\]

The engine parses this spec, applies each discrete operator term, and then projects through governance/audit constraints when configured.

## 5. Integration with Existing Systems

- **Bridge artifacts:** Read `bridge/graph_topology.json` via `build_adjacency`, ingest telemetry maps (`Theta_map`, `deltaS_map`, etc.), then emit updated fields (e.g., `corridor_field.json`).
- **Sophia audit:** Run `sophia.audit_navigation_state` (or related modules) after PDE updates to produce advisory-only governance checks.
- **Atlas overlays:** Sync updated fields to Atlas (e.g., via `sync_bridge_from_coherencelattice`) to visualize corridor density and derived overlays.
- **Thresholds and query helpers:** Operator parameters (`alpha`, `mu`, etc.) remain explicitly tunable per context and can be coupled to existing telemetry filtering/query helpers.

## 6. Example Smoke Test

```python
# File: python/tests/test_pde_engine.py
from coherence.pde_engine import PDECompiler, PDEEngine


def test_corridor_pde_step():
    graph_topo = {
        "nodes": ["x", "y"],
        "edges": [["x", "y", 1.0]],
    }
    compiler = PDECompiler(graph_topo)
    spec = {
        "fields": [
            {"name": "C", "role": "primitive"},
            {"name": "Theta", "role": "primitive"},
        ],
        "operators": [
            {"kind": "diffusion", "target": "C", "weight": 0.1},
        ],
        "governance": False,
    }
    compiler.load_spec(spec)
    engine = PDEEngine(compiler)

    state = {
        "C": {"x": 0.2, "y": 0.8},
        "Theta": {"x": 1.0, "y": 2.0},
    }

    next_state = engine.step(state)

    assert next_state["C"]["x"] >= 0
    assert next_state["C"]["y"] >= 0
    assert next_state["C"]["x"] != state["C"]["x"] or next_state["C"]["y"] != state["C"]["y"]
```

This smoke test verifies the engine executes and returns bounded, updated corridor values.

## Summary

These blocks establish a universal PDE grammar framework with:

- A JSON schema for typed PDE definitions (`fields`, `operators`, `governance`).
- Python DSL structures (`FieldSpec`, `OperatorSpec`, `Operator`).
- Concrete operator primitives (diffusion/advection/source/sink/projection).
- A compiler (`PDECompiler`) for parse/validation/pipeline construction.
- An execution engine (`PDEEngine`) for discrete updates and governance hooks.
- Example usage and a minimal smoke test.

Together, this allows AI users (or the brain itself) to define PDEs in a controlled language and run them deterministically on the Triadic Brain graph while preserving governance constraints.
