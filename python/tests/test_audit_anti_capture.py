from sophia.audit_anti_capture import audit_anti_capture


def test_audit_anti_capture_capture_risk_regime() -> None:
    findings = audit_anti_capture({"regime": "capture_risk", "risk_score": 0.72})

    assert findings == [
        {
            "law": "capture_risk_detected",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Governance capture risk rising.",
        }
    ]


def test_audit_anti_capture_oligarchic_drift_regime() -> None:
    findings = audit_anti_capture({"regime": "oligarchic_drift", "risk_score": 0.88})

    assert findings == [
        {
            "law": "oligarchic_drift_warning",
            "severity": "warn",
            "semanticMode": "non-executive",
            "message": "Power concentration and transparency decline detected.",
        }
    ]


def test_audit_anti_capture_systemic_capture_regime() -> None:
    findings = audit_anti_capture({"regime": "systemic_capture", "risk_score": 0.98})

    assert findings == [
        {
            "law": "systemic_capture_detected",
            "severity": "docket",
            "semanticMode": "non-executive",
            "message": "System approaching full capture dynamics.",
        }
    ]


def test_audit_anti_capture_no_findings_outside_capture_regimes() -> None:
    findings = audit_anti_capture({"regime": "stable", "risk_score": 0.1})

    assert findings == []
