from sophia.triadic_audit import audit_triadic_state


def test_triadic_audit_passes_clean_state() -> None:
    result = audit_triadic_state(
        {
            "entropy_extension": {"total_entropy": 0.1},
            "true_coherence": "coherent",
        }
    )

    assert result == {"audit_findings": [], "audit_pass": True}


def test_triadic_audit_flags_entropy_and_extractive_state() -> None:
    result = audit_triadic_state(
        {
            "entropy_extension": {"total_entropy": 0.3},
            "true_coherence": "extractive_coherence",
        }
    )

    assert result["audit_pass"] is False
    assert result["audit_findings"] == [
        "high_entropy_risk",
        "ethical_violation_possible",
    ]


def test_triadic_audit_flags_false_coherence() -> None:
    result = audit_triadic_state(
        {
            "entropy_extension": {"total_entropy": 0.05},
            "true_coherence": "false_coherence",
        }
    )

    assert result["audit_pass"] is False
    assert result["audit_findings"] == ["invalid_signal"]
