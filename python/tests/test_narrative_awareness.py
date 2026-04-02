from sophia.governance.narrative_awareness import interpret_narrative_overlay


def test_interpret_narrative_overlay_defaults() -> None:
    result = interpret_narrative_overlay({})

    assert result == {
        "narrative_flags": [],
        "care_bias": False,
        "anti_coercion_bias": False,
        "humanization_bias": False,
    }


def test_interpret_narrative_overlay_bias_flags() -> None:
    packet = {
        "narrative_overlay": {
            "activated_modules": [
                "care_system_constructor",
                "non_enslavement_constraint_kernel",
                "humanization_engine",
            ]
        }
    }

    result = interpret_narrative_overlay(packet)

    assert result["narrative_flags"] == packet["narrative_overlay"]["activated_modules"]
    assert result["care_bias"] is True
    assert result["anti_coercion_bias"] is True
    assert result["humanization_bias"] is True
