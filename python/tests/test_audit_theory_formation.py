from sophia.audit_theory_formation import audit_theories


def test_audit_theories_warns_on_negative_coherence_score():
    artifact = {
        "theories": [
            {"coherence_score": 0.2},
            {"coherence_score": -0.1},
            {"coherence_score": 0.0},
        ]
    }

    findings = audit_theories(artifact)

    assert findings == [
        {
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Theory reduces coherence.",
        }
    ]
