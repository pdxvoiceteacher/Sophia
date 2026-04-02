from sophia.hb02_audit import audit_hb02


def test_hb02_audit_passes_for_valid_result() -> None:
    result = audit_hb02(
        {
            "entropy_reduction": 0.2,
            "true_coherence": "coherent",
        }
    )

    assert result == {"audit_pass": True, "issues": []}


def test_hb02_audit_flags_negative_entropy_reduction() -> None:
    result = audit_hb02(
        {
            "entropy_reduction": -0.01,
            "true_coherence": "coherent",
        }
    )

    assert result["audit_pass"] is False
    assert result["issues"] == ["conditioning_failed"]


def test_hb02_audit_flags_false_coherence() -> None:
    result = audit_hb02(
        {
            "entropy_reduction": 0.1,
            "true_coherence": "false_coherence",
        }
    )

    assert result["audit_pass"] is False
    assert result["issues"] == ["invalid_cognition"]


def test_hb02_audit_flags_multiple_issues() -> None:
    result = audit_hb02(
        {
            "entropy_reduction": -0.1,
            "true_coherence": "false_coherence",
        }
    )

    assert result["audit_pass"] is False
    assert result["issues"] == ["conditioning_failed", "invalid_cognition"]
