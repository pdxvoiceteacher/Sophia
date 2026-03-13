from __future__ import annotations

from copy import deepcopy
from typing import Any

from .ast import BinaryOp, Constant, Expr, FieldRef, UnaryOp
from .operator import OperatorSpec, operator_registry


def parse_expr(node: Any) -> Expr:
    """Recursively parse a JSON-like expression node into the AST."""
    if isinstance(node, dict):
        if "field" in node:
            return FieldRef(str(node["field"]))
        if "const" in node:
            return Constant(float(node["const"]))
        if "op" in node:
            op = node["op"]
            if op in {"add", "sub", "mul", "div"}:
                return BinaryOp(op=op, left=parse_expr(node["left"]), right=parse_expr(node["right"]))
            if op in {"neg", "pos"}:
                return UnaryOp(op=op, operand=parse_expr(node["arg"]))
    raise ValueError(f"Invalid expression node: {node}")


def _field_roles(pde_spec: dict[str, Any]) -> dict[str, str]:
    roles: dict[str, str] = {}
    for field in pde_spec.get("fields", []):
        roles[str(field["name"])] = str(field["role"])
    return roles


def compile_pde_spec(pde_spec: dict[str, Any]) -> list[OperatorSpec]:
    """Compile a PDE spec dictionary into executable OperatorSpec instances."""
    roles = _field_roles(pde_spec)
    ops: list[OperatorSpec] = []

    for op_json in pde_spec.get("operators", []):
        name = str(op_json["name"])
        if name not in operator_registry.operators:
            raise KeyError(f"Unknown operator: {name}")

        base_spec = operator_registry.get(name)
        spec = deepcopy(base_spec)

        explicit_outputs = op_json.get("outputs")
        if explicit_outputs is not None:
            spec.outputs = [str(out) for out in explicit_outputs]

        for out in spec.outputs:
            role = roles.get(out)
            if role == "derived":
                raise ValueError(f"Operator '{name}' cannot write to derived field '{out}'")

        if "requires_governance" in op_json:
            spec.requires_governance = bool(op_json["requires_governance"])

        if "formula" in op_json:
            spec.formula = parse_expr(op_json["formula"])

        spec.parameters.update(op_json.get("parameters", {}))
        ops.append(spec)

    return ops
