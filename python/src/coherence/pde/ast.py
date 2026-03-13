from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Expr:
    """Base class for expression AST nodes."""


@dataclass(frozen=True)
class FieldRef(Expr):
    field: str


@dataclass(frozen=True)
class Constant(Expr):
    value: float


@dataclass(frozen=True)
class BinaryOp(Expr):
    op: str
    left: Expr
    right: Expr


@dataclass(frozen=True)
class UnaryOp(Expr):
    op: str
    operand: Expr


def eval_expr(expr: Expr, state: dict[str, float]) -> float:
    """Evaluate an expression AST given a mapping of scalar field values."""
    if isinstance(expr, FieldRef):
        return float(state.get(expr.field, 0.0))
    if isinstance(expr, Constant):
        return float(expr.value)
    if isinstance(expr, BinaryOp):
        left = eval_expr(expr.left, state)
        right = eval_expr(expr.right, state)
        if expr.op == "add":
            return left + right
        if expr.op == "sub":
            return left - right
        if expr.op == "mul":
            return left * right
        if expr.op == "div":
            return left / right if right != 0 else 0.0
        raise ValueError(f"Unknown binary op {expr.op}")
    if isinstance(expr, UnaryOp):
        value = eval_expr(expr.operand, state)
        if expr.op == "neg":
            return -value
        if expr.op == "pos":
            return value
        raise ValueError(f"Unknown unary op {expr.op}")
    raise TypeError(f"Unhandled Expr type: {type(expr)}")
