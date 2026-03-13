# Lean-safe discrete corridor PDE scaffold

This is the theorem-oriented version of the discovery corridor equation:

\[
\partial_tC=D_C\nabla^2C-\nabla\cdot(C\nabla\Theta)+\alpha|\nabla\Theta|^2+\beta[\partial_t\Theta]-\mu C-\nu(\Delta S+\Lambda)C-\chi C^3
\]

implemented as a graph update law.

________________________________________

## Suggested Lean module layout

```text
CoherenceLattice/
  Field/
    Basic.lean
    State.lean
    Potential.lean
    Graph.lean
    DiscreteCorridor.lean
    Theorems.lean
```

________________________________________

## CoherenceLattice/Field/Basic.lean

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace CoherenceLattice.Field

structure UnitScalar where
  val : ℝ
  zero_le : 0 ≤ val
  le_one : val ≤ 1
deriving Repr

def clamp01 (x : ℝ) : ℝ :=
  max 0 (min 1 x)

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := by
  dsimp [clamp01]
  exact le_max_left _ _

theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := by
  dsimp [clamp01]
  apply max_le_iff.mpr
  constructor
  · linarith
  · exact min_le_left _ _

def mkUnitScalar (x : ℝ) : UnitScalar :=
  ⟨clamp01 x, clamp01_nonneg x, clamp01_le_one x⟩

def positivePart (x : ℝ) : ℝ :=
  max x 0

theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  dsimp [positivePart]
  exact le_max_right _ _

end CoherenceLattice.Field
```

________________________________________

## CoherenceLattice/Field/State.lean

```lean
import CoherenceLattice.Field.Basic
import Mathlib.Tactic

namespace CoherenceLattice.Field

abbrev NodeId := String

/-
  Minimal local field state.

  Psi is derived from E and T.
  Corridor is itself treated as a bounded [0,1] local scalar.
-/
structure LocalFieldState where
  id : NodeId
  E : UnitScalar
  T : UnitScalar
  deltaS : ℝ
  lambdaCrit : ℝ
  Es : ℝ
  novelty : ℝ
  thetaDot : ℝ
  corridor : UnitScalar
deriving Repr

def psi (X : LocalFieldState) : ℝ :=
  X.E.val * X.T.val

theorem psi_nonneg (X : LocalFieldState) : 0 ≤ psi X := by
  dsimp [psi]
  nlinarith [X.E.zero_le, X.T.zero_le]

theorem psi_le_one (X : LocalFieldState) : psi X ≤ 1 := by
  dsimp [psi]
  nlinarith [X.E.zero_le, X.E.le_one, X.T.zero_le, X.T.le_one]

abbrev FieldConfig := NodeId → LocalFieldState

end CoherenceLattice.Field
```

________________________________________

## CoherenceLattice/Field/Potential.lean

```lean
import CoherenceLattice.Field.State
import Mathlib.Tactic

namespace CoherenceLattice.Field

/-
  Sign-constrained telemetry potential weights.
-/
structure ThetaWeights where
  wPsi : ℝ
  wE : ℝ
  wT : ℝ
  wEs : ℝ
  wDeltaS : ℝ
  wLambda : ℝ
  wNovelty : ℝ
  hPsi : 0 ≤ wPsi
  hE : 0 ≤ wE
  hT : 0 ≤ wT
  hEs : 0 ≤ wEs
  hDeltaS : 0 ≤ wDeltaS
  hLambda : 0 ≤ wLambda
  hNovelty : 0 ≤ wNovelty
deriving Repr

/-
  Telemetry-derived coherence potential field.
-/
def theta (W : ThetaWeights) (X : LocalFieldState) : ℝ :=
  W.wPsi * psi X
  + W.wE * X.E.val
  + W.wT * X.T.val
  + W.wEs * X.Es
  - W.wDeltaS * X.deltaS
  - W.wLambda * X.lambdaCrit
  + W.wNovelty * X.novelty

end CoherenceLattice.Field
```

________________________________________

## CoherenceLattice/Field/Graph.lean

```lean
import CoherenceLattice.Field.Potential
import Mathlib.Data.List.BigOperators
import Mathlib.Algebra.BigOperators.Ring

open scoped BigOperators

namespace CoherenceLattice.Field

/-
  Weighted graph over knowledge/TEL states.
-/
structure WeightedGraph where
  nbrs : NodeId → List NodeId
  weight : NodeId → NodeId → ℝ
  weight_nonneg : ∀ i j, 0 ≤ weight i j
deriving Repr

end CoherenceLattice.Field
```

________________________________________

## CoherenceLattice/Field/DiscreteCorridor.lean

```lean
import CoherenceLattice.Field.Graph
import Mathlib.Data.List.BigOperators
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

open scoped BigOperators

namespace CoherenceLattice.Field

/-
  Discrete graph-Laplacian-style diffusion term:
  Σ_j w_ij (C_j - C_i)
-/
def diffusionTerm (G : WeightedGraph) (σ : FieldConfig) (i : NodeId) : ℝ :=
  ((G.nbrs i).map (fun j => G.weight i j * ((σ j).corridor.val - (σ i).corridor.val))).sum

/-
  Edge flux used to approximate -div(C ∇Θ).
-/
def edgeFlux (G : WeightedGraph) (W : ThetaWeights) (σ : FieldConfig) (i j : NodeId) : ℝ :=
  G.weight i j
    * (((σ i).corridor.val + (σ j).corridor.val) / 2)
    * (theta W (σ j) - theta W (σ i))

def divergenceTerm (G : WeightedGraph) (W : ThetaWeights) (σ : FieldConfig) (i : NodeId) : ℝ :=
  ((G.nbrs i).map (fun j => edgeFlux G W σ i j)).sum

/-
  Gradient-energy source:
  Σ_j w_ij (Θ_j - Θ_i)^2
-/
def gradientEnergy (G : WeightedGraph) (W : ThetaWeights) (σ : FieldConfig) (i : NodeId) : ℝ :=
  ((G.nbrs i).map (fun j => G.weight i j * (theta W (σ j) - theta W (σ i))^2)).sum

theorem gradientEnergy_nonneg (G : WeightedGraph) (W : ThetaWeights) (σ : FieldConfig) (i : NodeId) :
    0 ≤ gradientEnergy G W σ i := by
  unfold gradientEnergy
  exact List.sum_nonneg (by
    intro a ha
    rcases List.mem_map.mp ha with ⟨j, hj, rfl⟩
    have hw : 0 ≤ G.weight i j := G.weight_nonneg i j
    have hs : 0 ≤ (theta W (σ j) - theta W (σ i))^2 := sq_nonneg _
    exact mul_nonneg hw hs
  )

def sourceTerm (α β : ℝ) (G : WeightedGraph) (W : ThetaWeights) (σ : FieldConfig) (i : NodeId) : ℝ :=
  α * gradientEnergy G W σ i
  + β * positivePart ((σ i).thetaDot)

def sinkTerm (μ ν χ : ℝ) (σ : FieldConfig) (i : NodeId) : ℝ :=
  let c := (σ i).corridor.val
  μ * c
  + ν * (positivePart ((σ i).deltaS) + positivePart ((σ i).lambdaCrit)) * c
  + χ * c^3

theorem sourceTerm_nonneg
  (α β : ℝ)
  (hα : 0 ≤ α)
  (hβ : 0 ≤ β)
  (G : WeightedGraph) (W : ThetaWeights) (σ : FieldConfig) (i : NodeId) :
  0 ≤ sourceTerm α β G W σ i := by
  unfold sourceTerm
  have hg : 0 ≤ gradientEnergy G W σ i := gradientEnergy_nonneg G W σ i
  have hp : 0 ≤ positivePart ((σ i).thetaDot) := positivePart_nonneg _
  nlinarith

/-
  Explicit Euler step for corridor density.
-/
def rawCorridorUpdate
  (η D α β μ ν χ : ℝ)
  (G : WeightedGraph)
  (W : ThetaWeights)
  (σ : FieldConfig)
  (i : NodeId) : ℝ :=
  let c := (σ i).corridor.val
  c + η * (
      D * diffusionTerm G σ i
      - divergenceTerm G W σ i
      + sourceTerm α β G W σ i
      - sinkTerm μ ν χ σ i
    )

def corridorNext
  (η D α β μ ν χ : ℝ)
  (G : WeightedGraph)
  (W : ThetaWeights)
  (σ : FieldConfig)
  (i : NodeId) : UnitScalar :=
  mkUnitScalar (rawCorridorUpdate η D α β μ ν χ G W σ i)

theorem corridorNext_bounded
  (η D α β μ ν χ : ℝ)
  (G : WeightedGraph)
  (W : ThetaWeights)
  (σ : FieldConfig)
  (i : NodeId) :
  0 ≤ (corridorNext η D α β μ ν χ G W σ i).val
  ∧ (corridorNext η D α β μ ν χ G W σ i).val ≤ 1 := by
  constructor
  · exact (corridorNext η D α β μ ν χ G W σ i).zero_le
  · exact (corridorNext η D α β μ ν χ G W σ i).le_one

theorem rawCorridorUpdate_ge_current
  (η D α β μ ν χ : ℝ)
  (hη : 0 ≤ η)
  (G : WeightedGraph)
  (W : ThetaWeights)
  (σ : FieldConfig)
  (i : NodeId)
  (hTransport :
    divergenceTerm G W σ i ≤ D * diffusionTerm G σ i)
  (hSourceSink :
    sinkTerm μ ν χ σ i ≤ sourceTerm α β G W σ i) :
  (σ i).corridor.val ≤ rawCorridorUpdate η D α β μ ν χ G W σ i := by
  unfold rawCorridorUpdate
  nlinarith

/-
  Threshold-first corridor predicate.
-/
structure CorridorThresholds where
  corridor_c : ℝ
  gradient_c : ℝ
deriving Repr

def CorridorCandidate
  (τ : CorridorThresholds)
  (G : WeightedGraph)
  (W : ThetaWeights)
  (σ : FieldConfig)
  (i : NodeId) : Prop :=
  τ.corridor_c < (σ i).corridor.val ∧
  τ.gradient_c < gradientEnergy G W σ i

end CoherenceLattice.Field
```

________________________________________

## CoherenceLattice/Field/Theorems.lean

```lean
import CoherenceLattice.Field.DiscreteCorridor

namespace CoherenceLattice.Field

theorem corridor_candidate_of_thresholds
  (τ : CorridorThresholds)
  (G : WeightedGraph)
  (W : ThetaWeights)
  (σ : FieldConfig)
  (i : NodeId)
  (hc : τ.corridor_c < (σ i).corridor.val)
  (hg : τ.gradient_c < gradientEnergy G W σ i) :
  CorridorCandidate τ G W σ i := by
  exact ⟨hc, hg⟩

/-
  If the raw update crosses the threshold and gradient-energy is already high,
  then the next state is corridor-capable after clamping.
-/
theorem corridor_candidate_after_growth
  (τ : CorridorThresholds)
  (η D α β μ ν χ : ℝ)
  (G : WeightedGraph)
  (W : ThetaWeights)
  (σ : FieldConfig)
  (i : NodeId)
  (hCross : τ.corridor_c < rawCorridorUpdate η D α β μ ν χ G W σ i)
  (hUpper : rawCorridorUpdate η D α β μ ν χ G W σ i ≤ 1)
  (hg : τ.gradient_c < gradientEnergy G W σ i) :
  CorridorCandidate τ G W
    (fun j =>
      if j = i then
        { (σ j) with corridor := mkUnitScalar (rawCorridorUpdate η D α β μ ν χ G W σ i) }
      else σ j)
    i := by
  constructor
  ·
    dsimp
    simp
    have hclamp : clamp01 (rawCorridorUpdate η D α β μ ν χ G W σ i)
      = rawCorridorUpdate η D α β μ ν χ G W σ i := by
      unfold clamp01
      have hnonneg : 0 ≤ rawCorridorUpdate η D α β μ ν χ G W σ i := by
        linarith [hCross]
      have hmin : min 1 (rawCorridorUpdate η D α β μ ν χ G W σ i)
          = rawCorridorUpdate η D α β μ ν χ G W σ i := by
        exact min_eq_right hUpper
      rw [hmin]
      exact max_eq_right hnonneg
    simpa [mkUnitScalar, hclamp] using hCross
  ·
    dsimp
    simp
    exact hg

end CoherenceLattice.Field
```

________________________________________

## 2. Matching Python runtime scaffold

This Python side matches the Lean structure directly.

### Suggested Python layout

```text
coherence_field/
├── __init__.py
├── basic.py
├── state.py
├── potential.py
├── graph.py
├── corridor.py
├── engine.py
└── tests/
    └── test_corridor_smoke.py
```

________________________________________

### coherence_field/basic.py

```python
from __future__ import annotations

from dataclasses import dataclass


def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))


def positive_part(x: float) -> float:
    return max(0.0, float(x))


@dataclass(frozen=True, slots=True)
class UnitScalar:
    val: float

    def __post_init__(self) -> None:
        if not (0.0 <= self.val <= 1.0):
            raise ValueError(f"UnitScalar out of bounds: {self.val}")

    @classmethod
    def from_float(cls, x: float) -> "UnitScalar":
        return cls(clamp01(x))
```

________________________________________

### coherence_field/state.py

```python
from __future__ import annotations

from dataclasses import dataclass

from .basic import UnitScalar


@dataclass(frozen=True, slots=True)
class LocalFieldState:
    id: str
    E: UnitScalar
    T: UnitScalar
    delta_s: float
    lambda_crit: float
    Es: float
    novelty: float
    theta_dot: float
    corridor: UnitScalar

    @property
    def psi(self) -> float:
        return self.E.val * self.T.val
```

________________________________________

### coherence_field/potential.py

```python
from __future__ import annotations

from dataclasses import dataclass

from .state import LocalFieldState


@dataclass(frozen=True, slots=True)
class ThetaWeights:
    w_psi: float
    w_E: float
    w_T: float
    w_Es: float
    w_delta_s: float
    w_lambda: float
    w_novelty: float

    def __post_init__(self) -> None:
        for name, value in (
            ("w_psi", self.w_psi),
            ("w_E", self.w_E),
            ("w_T", self.w_T),
            ("w_Es", self.w_Es),
            ("w_delta_s", self.w_delta_s),
            ("w_lambda", self.w_lambda),
            ("w_novelty", self.w_novelty),
        ):
            if value < 0:
                raise ValueError(f"{name} must be nonnegative, got {value}")


def theta(W: ThetaWeights, X: LocalFieldState) -> float:
    return (
        W.w_psi * X.psi
        + W.w_E * X.E.val
        + W.w_T * X.T.val
        + W.w_Es * X.Es
        - W.w_delta_s * X.delta_s
        - W.w_lambda * X.lambda_crit
        + W.w_novelty * X.novelty
    )
```

________________________________________

### coherence_field/graph.py

```python
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict


@dataclass(slots=True)
class WeightedGraph:
    adjacency: Dict[str, Dict[str, float]]

    def neighbors(self, node_id: str) -> list[str]:
        return sorted(self.adjacency.get(node_id, {}).keys())

    def weight(self, i: str, j: str) -> float:
        return float(self.adjacency.get(i, {}).get(j, 0.0))

    def validate_nonnegative(self) -> None:
        for i, nbrs in self.adjacency.items():
            for j, w in nbrs.items():
                if w < 0:
                    raise ValueError(f"Negative edge weight at ({i}, {j}): {w}")
```

________________________________________

### coherence_field/corridor.py

```python
from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum

from .basic import UnitScalar, positive_part
from .graph import WeightedGraph
from .potential import ThetaWeights, theta
from .state import LocalFieldState


@dataclass(frozen=True, slots=True)
class CorridorThresholds:
    corridor_c: float
    gradient_c: float


class CorridorRegime(str, Enum):
    DORMANT = "dormant"
    CANDIDATE = "candidate"


def diffusion_term(G: WeightedGraph, sigma: dict[str, LocalFieldState], i: str) -> float:
    ci = sigma[i].corridor.val
    return sum(
        G.weight(i, j) * (sigma[j].corridor.val - ci)
        for j in G.neighbors(i)
    )


def edge_flux(G: WeightedGraph, W: ThetaWeights, sigma: dict[str, LocalFieldState], i: str, j: str) -> float:
    ci = sigma[i].corridor.val
    cj = sigma[j].corridor.val
    avg_c = 0.5 * (ci + cj)
    return G.weight(i, j) * avg_c * (theta(W, sigma[j]) - theta(W, sigma[i]))


def divergence_term(G: WeightedGraph, W: ThetaWeights, sigma: dict[str, LocalFieldState], i: str) -> float:
    return sum(edge_flux(G, W, sigma, i, j) for j in G.neighbors(i))


def gradient_energy(G: WeightedGraph, W: ThetaWeights, sigma: dict[str, LocalFieldState], i: str) -> float:
    th_i = theta(W, sigma[i])
    return sum(
        G.weight(i, j) * (theta(W, sigma[j]) - th_i) ** 2
        for j in G.neighbors(i)
    )


def source_term(alpha: float, beta: float, G: WeightedGraph, W: ThetaWeights, sigma: dict[str, LocalFieldState], i: str) -> float:
    return alpha * gradient_energy(G, W, sigma, i) + beta * positive_part(sigma[i].theta_dot)


def sink_term(mu: float, nu: float, chi: float, sigma: dict[str, LocalFieldState], i: str) -> float:
    c = sigma[i].corridor.val
    destabilizer = positive_part(sigma[i].delta_s) + positive_part(sigma[i].lambda_crit)
    return mu * c + nu * destabilizer * c + chi * (c ** 3)


def raw_corridor_update(
    eta: float,
    D: float,
    alpha: float,
    beta: float,
    mu: float,
    nu: float,
    chi: float,
    G: WeightedGraph,
    W: ThetaWeights,
    sigma: dict[str, LocalFieldState],
    i: str,
) -> float:
    c = sigma[i].corridor.val
    return c + eta * (
        D * diffusion_term(G, sigma, i)
        - divergence_term(G, W, sigma, i)
        + source_term(alpha, beta, G, W, sigma, i)
        - sink_term(mu, nu, chi, sigma, i)
    )


def corridor_next(
    eta: float,
    D: float,
    alpha: float,
    beta: float,
    mu: float,
    nu: float,
    chi: float,
    G: WeightedGraph,
    W: ThetaWeights,
    sigma: dict[str, LocalFieldState],
    i: str,
) -> UnitScalar:
    return UnitScalar.from_float(
        raw_corridor_update(eta, D, alpha, beta, mu, nu, chi, G, W, sigma, i)
    )


def corridor_candidate(
    tau: CorridorThresholds,
    G: WeightedGraph,
    W: ThetaWeights,
    sigma: dict[str, LocalFieldState],
    i: str,
) -> bool:
    return (
        sigma[i].corridor.val > tau.corridor_c
        and gradient_energy(G, W, sigma, i) > tau.gradient_c
    )


def corridor_regime(
    tau: CorridorThresholds,
    G: WeightedGraph,
    W: ThetaWeights,
    sigma: dict[str, LocalFieldState],
    i: str,
) -> CorridorRegime:
    if corridor_candidate(tau, G, W, sigma, i):
        return CorridorRegime.CANDIDATE
    return CorridorRegime.DORMANT


def step_corridor_field(
    eta: float,
    D: float,
    alpha: float,
    beta: float,
    mu: float,
    nu: float,
    chi: float,
    G: WeightedGraph,
    W: ThetaWeights,
    sigma: dict[str, LocalFieldState],
) -> dict[str, LocalFieldState]:
    updated: dict[str, LocalFieldState] = {}

    for node_id, state in sorted(sigma.items()):
        next_c = corridor_next(eta, D, alpha, beta, mu, nu, chi, G, W, sigma, node_id)
        updated[node_id] = replace(state, corridor=next_c)

    return updated
```

________________________________________

### coherence_field/engine.py

```python
from __future__ import annotations

from .corridor import (
    CorridorThresholds,
    corridor_regime,
    gradient_energy,
    raw_corridor_update,
    step_corridor_field,
)
from .graph import WeightedGraph
from .potential import ThetaWeights, theta
from .state import LocalFieldState


def run_corridor_step(
    G: WeightedGraph,
    W: ThetaWeights,
    sigma: dict[str, LocalFieldState],
    tau: CorridorThresholds,
    *,
    eta: float = 0.2,
    D: float = 0.3,
    alpha: float = 0.8,
    beta: float = 0.4,
    mu: float = 0.2,
    nu: float = 0.3,
    chi: float = 0.1,
) -> dict:
    next_sigma = step_corridor_field(
        eta, D, alpha, beta, mu, nu, chi, G, W, sigma
    )

    nodes = []
    for node_id in sorted(next_sigma.keys()):
        nodes.append(
            {
                "id": node_id,
                "theta": theta(W, sigma[node_id]),
                "gradientEnergy": gradient_energy(G, W, sigma, node_id),
                "corridorBefore": sigma[node_id].corridor.val,
                "corridorRawAfter": raw_corridor_update(
                    eta, D, alpha, beta, mu, nu, chi, G, W, sigma, node_id
                ),
                "corridorAfter": next_sigma[node_id].corridor.val,
                "regimeAfter": corridor_regime(tau, G, W, next_sigma, node_id).value,
            }
        )

    return {
        "parameters": {
            "eta": eta,
            "D": D,
            "alpha": alpha,
            "beta": beta,
            "mu": mu,
            "nu": nu,
            "chi": chi,
        },
        "nodes": nodes,
    }
```

________________________________________

### coherence_field/tests/test_corridor_smoke.py

```python
from coherence_field.basic import UnitScalar
from coherence_field.corridor import CorridorThresholds
from coherence_field.engine import run_corridor_step
from coherence_field.graph import WeightedGraph
from coherence_field.potential import ThetaWeights
from coherence_field.state import LocalFieldState


def test_corridor_smoke():
    G = WeightedGraph(
        adjacency={
            "a": {"b": 1.0, "c": 0.5},
            "b": {"a": 1.0, "c": 1.0},
            "c": {"a": 0.5, "b": 1.0},
        }
    )
    G.validate_nonnegative()

    sigma = {
        "a": LocalFieldState(
            id="a",
            E=UnitScalar.from_float(0.8),
            T=UnitScalar.from_float(0.7),
            delta_s=0.2,
            lambda_crit=0.2,
            Es=0.7,
            novelty=0.8,
            theta_dot=0.3,
            corridor=UnitScalar.from_float(0.1),
        ),
        "b": LocalFieldState(
            id="b",
            E=UnitScalar.from_float(0.6),
            T=UnitScalar.from_float(0.6),
            delta_s=0.4,
            lambda_crit=0.3,
            Es=0.5,
            novelty=0.4,
            theta_dot=0.1,
            corridor=UnitScalar.from_float(0.1),
        ),
        "c": LocalFieldState(
            id="c",
            E=UnitScalar.from_float(0.3),
            T=UnitScalar.from_float(0.4),
            delta_s=0.8,
            lambda_crit=0.9,
            Es=-0.2,
            novelty=0.1,
            theta_dot=-0.1,
            corridor=UnitScalar.from_float(0.1),
        ),
    }

    W = ThetaWeights(
        w_psi=1.0,
        w_E=0.3,
        w_T=0.3,
        w_Es=0.2,
        w_delta_s=0.8,
        w_lambda=0.8,
        w_novelty=0.5,
    )

    tau = CorridorThresholds(
        corridor_c=0.15,
        gradient_c=0.02,
    )

    result = run_corridor_step(G, W, sigma, tau)
    assert "nodes" in result
    assert len(result["nodes"]) == 3
```
