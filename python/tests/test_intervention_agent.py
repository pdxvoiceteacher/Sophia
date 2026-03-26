from sophia.intervention_agent import sophia_intervention_agent


def test_intervention_agent_prioritizes_entropy_reduction() -> None:
    result = sophia_intervention_agent(
        {
            "entropy_extension": {"external_entropy": 0.2},
            "field_ethics": {"empathy": 0.1},
        }
    )

    assert result == {
        "action": "reduce_entropy",
        "priority": "high",
        "reason": "external_entropy_exceeds_threshold",
    }


def test_intervention_agent_increases_empathy_when_needed() -> None:
    result = sophia_intervention_agent(
        {
            "entropy_extension": {"external_entropy": 0.05},
            "field_ethics": {"empathy": 0.4},
        }
    )

    assert result == {
        "action": "increase_empathy_weight",
        "priority": "medium",
        "reason": "low_empathy_detected",
    }


def test_intervention_agent_maintains_state_when_stable() -> None:
    result = sophia_intervention_agent(
        {
            "entropy_extension": {"external_entropy": 0.01},
            "field_ethics": {"empathy": 0.9},
        }
    )

    assert result == {
        "action": "maintain_state",
        "priority": "low",
    }
