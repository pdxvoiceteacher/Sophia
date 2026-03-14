"""Typed PDE grammar, compiler, and runtime for coherence field updates."""

from .ast import BinaryOp, Constant, Expr, FieldRef, UnaryOp, eval_expr
from .compiler import compile_pde_spec, parse_expr
from .engine import default_governance_projection, step_pde
from .operator import OperatorRegistry, OperatorSpec, operator_registry

# Import side-effect registrations.
from . import operators_corridor as _operators_corridor

__all__ = [
    "BinaryOp",
    "Constant",
    "Expr",
    "FieldRef",
    "UnaryOp",
    "eval_expr",
    "compile_pde_spec",
    "parse_expr",
    "default_governance_projection",
    "step_pde",
    "OperatorRegistry",
    "OperatorSpec",
    "operator_registry",
]
