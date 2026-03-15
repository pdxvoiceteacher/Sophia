from sophia.audit_theory_evolution import audit_theory_evolution


def test_audit_theory_evolution_warns_when_theory_pool_empty() -> None:
    findings = audit_theory_evolution({"theories": []})

    assert findings == [
        {
            "law": "theory_ecosystem_extinction",
            "severity": "warn",
            "semanticMode": "non-executive",
            "message": "No theories remain in evolutionary pool.",
        }
    ]


def test_audit_theory_evolution_no_findings_when_theories_present() -> None:
    findings = audit_theory_evolution({"theories": [{"id": "theory_1"}]})

    assert findings == []
