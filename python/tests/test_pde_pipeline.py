from __future__ import annotations

import pytest

from coherence.pde import compile_pde_spec, step_pde


def test_compile_and_step_formula_operator() -> None:
    pde_spec = {
        "fields": [
            {"name": "alpha", "role": "primitive"},
            {"name": "deltaPsi", "role": "primitive"},
            {"name": "C", "role": "primitive"},
        ],
        "operators": [
            {
                "name": "alpha_source",
                "formula": {
                    "op": "mul",
                    "left": {"field": "alpha"},
                    "right": {"field": "deltaPsi"},
                },
            }
        ],
    }
    ops = compile_pde_spec(pde_spec)
    state = {"alpha": 0.5, "deltaPsi": 0.2, "C": 0.1}

    next_state = step_pde(state, ops, dt=0.1)

    assert next_state["C"] == pytest.approx(0.11)


def test_compile_rejects_writes_to_derived_field() -> None:
    pde_spec = {
        "fields": [
            {"name": "C", "role": "primitive"},
            {"name": "Psi", "role": "derived"},
        ],
        "operators": [
            {"name": "graph_diffusion", "outputs": ["Psi"]}
        ],
    }

    with pytest.raises(ValueError, match="cannot write to derived field"):
        compile_pde_spec(pde_spec)


def test_governance_required_operator_blocked_when_disabled() -> None:
    pde_spec = {
        "fields": [{"name": "C", "role": "primitive"}],
        "operators": [{"name": "graph_diffusion", "requires_governance": True}],
    }
    ops = compile_pde_spec(pde_spec)

    with pytest.raises(PermissionError, match="requires governance"):
        step_pde({"C": 0.25}, ops, governance_enabled=False)


def test_governance_projection_clamps_state() -> None:
    pde_spec = {
        "fields": [
            {"name": "alpha", "role": "primitive"},
            {"name": "deltaPsi", "role": "primitive"},
            {"name": "C", "role": "primitive"},
        ],
        "operators": [
            {
                "name": "alpha_source",
                "formula": {
                    "op": "mul",
                    "left": {"const": 5.0},
                    "right": {"field": "alpha"},
                },
            }
        ],
    }
    ops = compile_pde_spec(pde_spec)

    next_state = step_pde({"alpha": 1.0, "deltaPsi": 0.0, "C": 0.9}, ops, governance_enabled=True)

    assert next_state["C"] == 1.0
