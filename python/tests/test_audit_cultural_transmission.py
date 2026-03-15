from sophia.audit_cultural_transmission import audit_cultural_transmission


def test_audit_cultural_transmission_flags_low_understanding() -> None:
    findings = audit_cultural_transmission({"metrics": {"understanding": 0.19}})

    assert findings == [
        {
            "law": "low_public_understanding",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Theory adoption limited by low public comprehension.",
        }
    ]


def test_audit_cultural_transmission_no_findings_at_threshold() -> None:
    findings = audit_cultural_transmission({"metrics": {"understanding": 0.2}})

    assert findings == []


def test_audit_cultural_transmission_defaults_to_low_understanding_when_missing() -> None:
    findings = audit_cultural_transmission({})

    assert findings == [
        {
            "law": "low_public_understanding",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Theory adoption limited by low public comprehension.",
        }
    ]
