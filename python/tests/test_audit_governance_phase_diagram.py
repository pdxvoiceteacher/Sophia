from sophia.audit_governance_phase_diagram import audit_governance_phase_diagram


def test_audit_governance_phase_diagram_flags_rupture_regions() -> None:
    artifact = {
        "surface": [
            {"regime": "stable_terrace", "x": 0.2},
            {"regime": "civilizational_rupture", "x": 0.8},
        ]
    }

    findings = audit_governance_phase_diagram(artifact)

    assert findings == [
        {
            "law": "governance_instability_region",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Phase diagram contains civilizational rupture regions.",
        }
    ]


def test_audit_governance_phase_diagram_no_findings_without_rupture() -> None:
    artifact = {
        "surface": [
            {"regime": "stable_terrace", "x": 0.2},
            {"regime": "orthodoxy_drift", "x": 0.5},
        ]
    }

    findings = audit_governance_phase_diagram(artifact)

    assert findings == []


def test_audit_governance_phase_diagram_no_findings_when_surface_missing() -> None:
    findings = audit_governance_phase_diagram({})

    assert findings == []
