from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable

from .ast import Expr


@dataclass
class OperatorSpec:
    """Metadata for a PDE operator and its bound implementation."""

    name: str
    inputs: list[str]
    outputs: list[str]
    locality: str
    reversible: bool
    dissipative: bool
    requires_governance: bool = False
    apply: Callable[[dict[str, float], dict[str, float]], None] = field(
        default=lambda *_args, **_kwargs: None
    )
    formula: Expr | None = None
    parameters: dict[str, Any] = field(default_factory=dict)


class OperatorRegistry:
    """Registry of available PDE operators."""

    def __init__(self) -> None:
        self.operators: dict[str, OperatorSpec] = {}

    def register(self, spec: OperatorSpec) -> None:
        self.operators[spec.name] = spec

    def get(self, name: str) -> OperatorSpec:
        return self.operators[name]


operator_registry = OperatorRegistry()


def diffusion_apply(_state: dict[str, float], _delta: dict[str, float]) -> None:
    """Placeholder for scalar diffusion; graph implementation belongs in corridor operators."""


diffusion_spec = OperatorSpec(
    name="graph_diffusion",
    inputs=["C"],
    outputs=["C"],
    locality="edge",
    reversible=False,
    dissipative=True,
    requires_governance=False,
    apply=diffusion_apply,
)
operator_registry.register(diffusion_spec)


def alpha_source_apply(state: dict[str, float], delta: dict[str, float]) -> None:
    alpha = state.get("alpha", 0.0)
    delta_psi = state.get("deltaPsi", 0.0)
    delta["C"] = delta.get("C", 0.0) + (alpha * delta_psi)


alpha_source_spec = OperatorSpec(
    name="alpha_source",
    inputs=["alpha", "deltaPsi"],
    outputs=["C"],
    locality="node",
    reversible=False,
    dissipative=False,
    apply=alpha_source_apply,
)
operator_registry.register(alpha_source_spec)
