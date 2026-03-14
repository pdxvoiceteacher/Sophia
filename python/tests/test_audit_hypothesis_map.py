from sophia.audit_hypothesis_map import audit_hypotheses


def test_audit_hypotheses_no_hypotheses_generated():
    artifact = {"summary": {"count": 0}}

    findings = audit_hypotheses(artifact)

    assert findings == [
        {
            "severity": "info",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "No hypotheses generated.",
        }
    ]
