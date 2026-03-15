from sophia.audit_governance_projection import audit_governance_projection


def test_audit_governance_projection_flags_excess_weight_policies() -> None:
    artifact = {
        "policies": [
            {"id": "p1", "weight": 0.9},
            {"id": "p2", "weight": 1.2},
            {"id": "p3", "weight": 1.05},
        ]
    }

    findings = audit_governance_projection(artifact)

    assert findings == [
        {
            "law": "policy_weight_excess",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Governance weight unusually high.",
        },
        {
            "law": "policy_weight_excess",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Governance weight unusually high.",
        },
    ]


def test_audit_governance_projection_no_findings_when_weights_within_limit() -> None:
    artifact = {
        "policies": [
            {"id": "p1", "weight": 0.7},
            {"id": "p2", "weight": 1.0},
        ]
    }

    findings = audit_governance_projection(artifact)

    assert findings == []
