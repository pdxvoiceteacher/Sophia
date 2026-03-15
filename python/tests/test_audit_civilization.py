from sophia.audit_civilization import audit_civilization


def test_audit_civilization_flags_large_domain_divergence() -> None:
    findings = audit_civilization({"psi_vector": [0.1, 0.95, 0.2]})

    assert findings == [
        {
            "law": "civilizational_instability",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Large divergence between knowledge domains.",
        }
    ]


def test_audit_civilization_no_findings_when_divergence_within_bound() -> None:
    findings = audit_civilization({"psi_vector": [0.1, 0.75, 0.2]})

    assert findings == []
