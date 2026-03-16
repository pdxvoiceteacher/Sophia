from sophia.audit_governance_stability import audit_governance_stability


def test_audit_governance_stability_unstable_discovery() -> None:
    findings = audit_governance_stability({"regime": "unstable_discovery"})

    assert findings == [
        {
            "law": "governance_instability_warning",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Discovery ecosystem becoming unstable.",
        }
    ]


def test_audit_governance_stability_pre_capture_drift() -> None:
    findings = audit_governance_stability({"regime": "pre_capture_drift"})

    assert findings == [
        {
            "law": "capture_drift_warning",
            "severity": "warn",
            "semanticMode": "non-executive",
            "message": "Governance capture risk rising.",
        }
    ]


def test_audit_governance_stability_systemic_instability() -> None:
    findings = audit_governance_stability({"regime": "systemic_instability"})

    assert findings == [
        {
            "law": "civilizational_instability",
            "severity": "docket",
            "semanticMode": "non-executive",
            "message": "Discovery ecosystem destabilized.",
        }
    ]


def test_audit_governance_stability_no_findings_for_stable_regime() -> None:
    findings = audit_governance_stability({"regime": "stable"})

    assert findings == []
