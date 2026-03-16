from sophia.audit_simulation import audit_simulation


def test_audit_simulation_warns_on_low_civilizational_signal() -> None:
    findings = audit_simulation({"S_civ": 0.19})

    assert findings == [
        {
            "law": "civilization_collapse_risk",
            "severity": "warn",
            "semanticMode": "non-executive",
        }
    ]


def test_audit_simulation_no_findings_above_threshold() -> None:
    findings = audit_simulation({"S_civ": 0.2})

    assert findings == []


def test_audit_simulation_defaults_to_warning_when_signal_missing() -> None:
    findings = audit_simulation({})

    assert findings == [
        {
            "law": "civilization_collapse_risk",
            "severity": "warn",
            "semanticMode": "non-executive",
        }
    ]
