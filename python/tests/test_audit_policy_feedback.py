from sophia.audit_policy_feedback import audit_policy_feedback


def test_audit_policy_feedback_flags_overbias_when_pressure_exceeds_limit() -> None:
    findings = audit_policy_feedback({"policy_pressure": [0.9, 1.2, 1.7]})

    assert findings == [
        {
            "law": "policy_overbias",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Policy pressure may excessively bias discovery.",
        }
    ]


def test_audit_policy_feedback_no_findings_when_pressure_within_limit() -> None:
    findings = audit_policy_feedback({"policy_pressure": [0.4, 1.0, 1.5]})

    assert findings == []
