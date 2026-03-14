from sophia.audit_hypothesis_tests import audit_hypothesis_tests


def test_audit_hypothesis_tests_warns_on_negative_psi_gain():
    artifact = {
        "tests": [
            {"psi_gain": 0.1},
            {"psi_gain": -0.2},
            {"psi_gain": 0.0},
        ]
    }

    findings = audit_hypothesis_tests(artifact)

    assert findings == [
        {
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Hypothesis reduced coherence.",
        }
    ]
