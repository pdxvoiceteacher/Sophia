from sophia.audit_corridor_confidence import audit_corridor_confidence


def test_audit_corridor_confidence_flags_low_confidence_corridors() -> None:
    artifact = {
        "corridors": [
            {"topic": "quantum", "confidence": 0.12},
            {"topic": "biology", "confidence": 0.65},
            {"topic": "ai", "confidence": 0.05},
        ]
    }

    findings = audit_corridor_confidence(artifact)

    assert findings == [
        {
            "law": "weak_discovery_signal",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Low confidence corridor for quantum",
        },
        {
            "law": "weak_discovery_signal",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Low confidence corridor for ai",
        },
    ]


def test_audit_corridor_confidence_no_findings_when_confidence_is_sufficient() -> None:
    artifact = {
        "corridors": [
            {"topic": "physics", "confidence": 0.2},
            {"topic": "math", "confidence": 0.9},
        ]
    }

    findings = audit_corridor_confidence(artifact)

    assert findings == []


def test_audit_corridor_confidence_no_findings_when_no_corridors() -> None:
    findings = audit_corridor_confidence({})

    assert findings == []
