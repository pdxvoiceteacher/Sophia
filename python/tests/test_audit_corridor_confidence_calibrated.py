from sophia.audit_corridor_confidence_calibrated import audit_corridor_confidence_calibrated


def test_audit_corridor_confidence_calibrated_flags_overconfidence() -> None:
    artifact = {
        "corridors": [
            {"topic": "quantum", "confidence": 0.96},
            {"topic": "biology", "confidence": 0.91},
            {"topic": "ai", "confidence": 0.99},
        ]
    }

    findings = audit_corridor_confidence_calibrated(artifact)

    assert findings == [
        {
            "law": "overconfidence_risk",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Confidence extremely high; verify calibration.",
        },
        {
            "law": "overconfidence_risk",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Confidence extremely high; verify calibration.",
        },
    ]


def test_audit_corridor_confidence_calibrated_no_findings_at_threshold() -> None:
    artifact = {
        "corridors": [
            {"topic": "physics", "confidence": 0.95},
            {"topic": "math", "confidence": 0.9},
        ]
    }

    findings = audit_corridor_confidence_calibrated(artifact)

    assert findings == []


def test_audit_corridor_confidence_calibrated_no_findings_when_no_corridors() -> None:
    findings = audit_corridor_confidence_calibrated({})

    assert findings == []
