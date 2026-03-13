from __future__ import annotations

from .operator import OperatorSpec, operator_registry


def compute_graph_laplacian(state: dict[str, float], delta: dict[str, float]) -> None:
    c = state.get("C", 0.0)
    neighbor_avg = state.get("C_neighbor_avg", c)
    delta["C"] = delta.get("C", 0.0) + (neighbor_avg - c)


laplacian_spec = OperatorSpec(
    name="graph_laplacian",
    inputs=["C", "C_neighbor_avg"],
    outputs=["C"],
    locality="edge",
    reversible=False,
    dissipative=True,
    apply=compute_graph_laplacian,
)
operator_registry.register(laplacian_spec)


def compute_gradient_source(state: dict[str, float], delta: dict[str, float]) -> None:
    alpha = state.get("alpha", 0.0)
    grad_theta_sq = state.get("gradThetaSq", 0.0)
    delta["C"] = delta.get("C", 0.0) + alpha * grad_theta_sq


gradient_spec = OperatorSpec(
    name="gradient_energy_source",
    inputs=["alpha", "gradThetaSq"],
    outputs=["C"],
    locality="edge",
    reversible=False,
    dissipative=False,
    apply=compute_gradient_source,
)
operator_registry.register(gradient_spec)
