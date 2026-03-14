from sophia.audit_paradigm_shift import audit_paradigm_shift


def test_audit_paradigm_shift_watch_when_no_new_corridors():
    artifact = {"new_corridors": 0}

    findings = audit_paradigm_shift(artifact)

    assert findings == [
        {
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Rupture detected but no new corridors formed.",
        }
    ]
