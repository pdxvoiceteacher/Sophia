from __future__ import annotations

import pytest

from coherence.bridge.pde_grammar import (
    FieldExpr,
    MulExpr,
    compile_pde_spec,
    step_pde,
)


def _state() -> dict[str, dict[str, float]]:
    return {
        "adjacency": {
            "n0": [("n1", 1.0)],
            "n1": [("n0", 1.0)],
        },
        "C": {"n0": 0.2, "n1": 0.6},
        "Theta": {"n0": 0.1, "n1": 0.3},
        "Theta_dot": {"n0": 0.2, "n1": -0.1},
        "DeltaS": {"n0": 0.1, "n1": 0.2},
        "Lambda": {"n0": 0.1, "n1": 0.0},
        "E": {"n0": 0.5, "n1": 0.4},
        "T": {"n0": 0.8, "n1": 0.2},
    }


def test_compile_rejects_derived_output() -> None:
    spec = {
        "fields": [{"name": "C", "role": "derived"}],
        "operators": [{"name": "graph_diffusion"}],
    }

    with pytest.raises(ValueError, match="cannot write to derived field"):
        compile_pde_spec(spec, governance_enabled=True)


def test_compile_rejects_unknown_operator() -> None:
    spec = {
        "fields": [{"name": "C", "role": "primitive"}],
        "operators": [{"name": "missing_op"}],
    }

    with pytest.raises(KeyError, match="Unknown operator"):
        compile_pde_spec(spec, governance_enabled=True)


def test_step_updates_c_and_recomputes_derived() -> None:
    spec = {
        "fields": [
            {"name": "C", "role": "primitive"},
            {"name": "Psi", "role": "derived"},
        ],
        "operators": [
            {"name": "graph_diffusion", "coefficient": 0.2},
            {"name": "gradient_source", "coefficient": 0.1},
            {"name": "theta_time_source", "coefficient": 0.3},
        ],
    }
    compiled = compile_pde_spec(spec, governance_enabled=True)

    new_state = step_pde(
        _state(),
        compiled,
        dt=0.1,
        weights={"mu": 0.05, "nu": 0.2, "chi": 0.01},
        derived_formulas={"Psi": MulExpr(FieldExpr("E"), FieldExpr("T"))},
    )

    assert new_state["C"]["n0"] != pytest.approx(0.2)
    assert new_state["C"]["n1"] != pytest.approx(0.6)
    assert new_state["Psi"]["n0"] == pytest.approx(0.4)
    assert new_state["Psi"]["n1"] == pytest.approx(0.08)


def test_governance_projection_is_applied() -> None:
    spec = {
        "fields": [{"name": "C", "role": "primitive"}],
        "operators": [{"name": "theta_time_source", "coefficient": 10.0}],
    }
    compiled = compile_pde_spec(spec, governance_enabled=True)

    state = _state()
    state["C"] = {"n0": 0.9, "n1": 0.95}

    def projection(payload: dict[str, dict[str, float]]) -> dict[str, dict[str, float]]:
        payload["C"] = {k: 0.5 for k in payload["C"]}
        return payload

    new_state = step_pde(
        state,
        compiled,
        dt=1.0,
        weights={},
        governance_projection=projection,
    )

    assert new_state["C"] == {"n0": 0.5, "n1": 0.5}
