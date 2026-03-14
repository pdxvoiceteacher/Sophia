from __future__ import annotations

from typing import Callable

from .ast import eval_expr
from .operator import OperatorSpec


def default_governance_projection(state: dict[str, float]) -> dict[str, float]:
    """Default governance projection: clamp all state values to [0, 1]."""
    return {field: max(0.0, min(1.0, value)) for field, value in state.items()}


def step_pde(
    state: dict[str, float],
    pde_ops: list[OperatorSpec],
    dt: float = 0.1,
    governance_enabled: bool = False,
    governance_projection: Callable[[dict[str, float]], dict[str, float]] | None = None,
) -> dict[str, float]:
    """Run one explicit-Euler PDE step over scalar field state."""
    delta: dict[str, float] = {field: 0.0 for field in state}

    for op in pde_ops:
        if op.requires_governance and not governance_enabled:
            raise PermissionError(
                f"Operator '{op.name}' requires governance but governance is disabled"
            )

        if op.formula is not None:
            contribution = eval_expr(op.formula, state)
            for out in op.outputs:
                delta[out] = delta.get(out, 0.0) + contribution
        else:
            op.apply(state, delta)

    new_state = {
        field: value + dt * delta.get(field, 0.0)
        for field, value in state.items()
    }

    if governance_enabled:
        projection = governance_projection or default_governance_projection
        return projection(new_state)

    return new_state
