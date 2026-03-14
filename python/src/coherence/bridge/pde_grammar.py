from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


@dataclass(frozen=True)
class Expr:
    """Base class for typed PDE expression nodes."""


@dataclass(frozen=True)
class FieldExpr(Expr):
    field: str


@dataclass(frozen=True)
class ConstExpr(Expr):
    value: float


@dataclass(frozen=True)
class AddExpr(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class MulExpr(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class DivExpr(Expr):
    left: Expr
    right: Expr


def eval_expr(expr: Expr, values: dict[str, float]) -> float:
    """Evaluate typed expression AST over scalar node values."""
    if isinstance(expr, FieldExpr):
        return float(values.get(expr.field, 0.0))
    if isinstance(expr, ConstExpr):
        return float(expr.value)
    if isinstance(expr, AddExpr):
        return eval_expr(expr.left, values) + eval_expr(expr.right, values)
    if isinstance(expr, MulExpr):
        return eval_expr(expr.left, values) * eval_expr(expr.right, values)
    if isinstance(expr, DivExpr):
        denom = eval_expr(expr.right, values)
        if denom == 0:
            return 0.0
        return eval_expr(expr.left, values) / denom
    raise TypeError(f"Unhandled expression type: {type(expr)}")


@dataclass(frozen=True)
class OperatorSpec:
    name: str
    inputs: list[str]
    outputs: list[str]
    locality: str
    op_type: str
    governance: str


@dataclass(frozen=True)
class CompiledOperator:
    spec: OperatorSpec
    coefficient: float = 1.0


OPERATOR_REGISTRY: dict[str, OperatorSpec] = {
    "graph_diffusion": OperatorSpec(
        name="graph_diffusion",
        inputs=["C"],
        outputs=["C"],
        locality="edge-local",
        op_type="diffusion",
        governance="safe",
    ),
    "advective_flux": OperatorSpec(
        name="advective_flux",
        inputs=["C", "Theta"],
        outputs=["C"],
        locality="edge-local",
        op_type="advection",
        governance="safe",
    ),
    "gradient_source": OperatorSpec(
        name="gradient_source",
        inputs=["Theta"],
        outputs=["C"],
        locality="edge-local",
        op_type="source",
        governance="safe",
    ),
    "theta_time_source": OperatorSpec(
        name="theta_time_source",
        inputs=["Theta_dot"],
        outputs=["C"],
        locality="node-local",
        op_type="time_deriv",
        governance="safe",
    ),
}


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def apply_operator(spec: OperatorSpec, state: dict[str, dict[str, float]]) -> dict[str, dict[str, float]]:
    """Apply one built-in operator and return field contribution maps."""
    contributions = {field: {} for field in spec.outputs}
    adjacency = state.get("adjacency", {})

    if spec.op_type == "diffusion":
        c_vals = state.get("C", {})
        laplacian: dict[str, float] = {}
        for node, nbrs in adjacency.items():
            c_i = c_vals.get(node, 0.0)
            degree = sum(weight for _, weight in nbrs)
            total = degree * c_i
            for nbr, weight in nbrs:
                total -= weight * c_vals.get(nbr, 0.0)
            laplacian[node] = total
        contributions["C"] = laplacian

    elif spec.op_type == "advection":
        theta_vals = state.get("Theta", {})
        c_vals = state.get("C", {})
        div_flux: dict[str, float] = {}
        for node, nbrs in adjacency.items():
            c_i = c_vals.get(node, 0.0)
            flux_sum = 0.0
            for nbr, weight in nbrs:
                c_j = c_vals.get(nbr, 0.0)
                avg_c = 0.5 * (c_i + c_j)
                flux_sum += weight * avg_c * (theta_vals.get(nbr, 0.0) - theta_vals.get(node, 0.0))
            div_flux[node] = -flux_sum
        contributions["C"] = div_flux

    elif spec.op_type == "source":
        theta_vals = state.get("Theta", {})
        src: dict[str, float] = {}
        for node, nbrs in adjacency.items():
            grad_energy = 0.0
            for nbr, weight in nbrs:
                diff = theta_vals.get(nbr, 0.0) - theta_vals.get(node, 0.0)
                grad_energy += weight * (diff * diff)
            src[node] = grad_energy
        contributions["C"] = src

    elif spec.op_type == "time_deriv":
        theta_dot = state.get("Theta_dot", {})
        contributions["C"] = {node: max(value, 0.0) for node, value in theta_dot.items()}

    return contributions


def compile_pde_spec(
    spec: dict,
    *,
    governance_enabled: bool,
    operator_registry: dict[str, OperatorSpec] | None = None,
) -> list[CompiledOperator]:
    """Compile JSON-like spec into operators with compile-time checks."""
    registry = operator_registry or OPERATOR_REGISTRY
    fields = {f["name"]: f.get("role", "primitive") for f in spec.get("fields", [])}

    compiled: list[CompiledOperator] = []
    for item in spec.get("operators", []):
        name = item["name"]
        if name not in registry:
            raise KeyError(f"Unknown operator: {name}")

        op = registry[name]
        for out_field in op.outputs:
            if fields.get(out_field) == "derived":
                raise ValueError(f"Operator '{name}' cannot write to derived field '{out_field}'")

        if op.governance == "risky" and not governance_enabled:
            raise PermissionError(f"Operator '{name}' requires governance-enabled execution")

        compiled.append(CompiledOperator(spec=op, coefficient=float(item.get("coefficient", 1.0))))

    return compiled


def recompute_derived_fields(
    state: dict[str, dict[str, float]],
    derived_formulas: dict[str, Expr],
) -> None:
    """Recompute derived fields from formulas so operators never write them directly."""
    node_ids: set[str] = set()
    for values in state.values():
        if isinstance(values, dict):
            node_ids.update(values.keys())

    for field, expr in derived_formulas.items():
        computed: dict[str, float] = {}
        for node in node_ids:
            row = {name: values.get(node, 0.0) for name, values in state.items() if isinstance(values, dict)}
            computed[node] = eval_expr(expr, row)
        state[field] = computed


def step_pde(
    state: dict[str, dict[str, float]],
    operators: list[CompiledOperator],
    *,
    dt: float,
    weights: dict[str, float],
    governance_projection: Callable[[dict[str, dict[str, float]]], dict[str, dict[str, float]]] | None = None,
    derived_formulas: dict[str, Expr] | None = None,
) -> dict[str, dict[str, float]]:
    """Apply one PDE step: weighted contributions + sinks + governance + derived recompute."""
    total: dict[str, dict[str, float]] = {}
    for compiled in operators:
        contribs = apply_operator(compiled.spec, state)
        weight = compiled.coefficient * weights.get(compiled.spec.name, 1.0)
        for field, delta_map in contribs.items():
            acc = total.setdefault(field, {})
            for node, delta in delta_map.items():
                acc[node] = acc.get(node, 0.0) + weight * delta

    c_vals = state.get("C", {})
    delta_s = state.get("DeltaS", {})
    lambdas = state.get("Lambda", {})
    mu = float(weights.get("mu", 0.0))
    nu = float(weights.get("nu", 0.0))
    chi = float(weights.get("chi", 0.0))

    c_delta = total.setdefault("C", {})
    for node, c_i in c_vals.items():
        decay = mu * c_i
        suppress = nu * (max(delta_s.get(node, 0.0), 0.0) + max(lambdas.get(node, 0.0), 0.0)) * c_i
        saturation = chi * (c_i ** 3)
        c_delta[node] = c_delta.get(node, 0.0) - (decay + suppress + saturation)

    new_state = {k: (v.copy() if isinstance(v, dict) else v) for k, v in state.items()}
    new_c: dict[str, float] = {}
    for node, c_i in c_vals.items():
        new_c[node] = _clamp01(c_i + dt * c_delta.get(node, 0.0))
    new_state["C"] = new_c

    if governance_projection is not None:
        new_state = governance_projection(new_state)

    if derived_formulas:
        recompute_derived_fields(new_state, derived_formulas)

    return new_state
