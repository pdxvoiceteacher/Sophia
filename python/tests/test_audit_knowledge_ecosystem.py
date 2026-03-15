from sophia.audit_knowledge_ecosystem import audit_knowledge_ecosystem


def test_audit_knowledge_ecosystem_stagnation_regime() -> None:
    findings = audit_knowledge_ecosystem({"regime": "stagnation"})

    assert findings == [
        {
            "law": "knowledge_stagnation",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Knowledge ecosystem stagnating.",
        }
    ]


def test_audit_knowledge_ecosystem_fragmentation_regime() -> None:
    findings = audit_knowledge_ecosystem({"regime": "fragmentation"})

    assert findings == [
        {
            "law": "knowledge_fragmentation",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Paradigm space fragmented.",
        }
    ]


def test_audit_knowledge_ecosystem_other_regime_no_findings() -> None:
    findings = audit_knowledge_ecosystem({"regime": "stable"})

    assert findings == []
