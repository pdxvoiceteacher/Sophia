from sophia.audit_paradigm_competition import audit_paradigm_competition


def test_audit_paradigm_competition_emits_fragmentation_finding_above_limit() -> None:
    terraces = [{"id": f"t{i}"} for i in range(6)]

    findings = audit_paradigm_competition(terraces)

    assert findings == [
        {
            "law": "paradigm_fragmentation",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Too many competing terraces detected.",
        }
    ]


def test_audit_paradigm_competition_no_findings_at_limit() -> None:
    terraces = [{"id": f"t{i}"} for i in range(5)]

    findings = audit_paradigm_competition(terraces)

    assert findings == []


def test_audit_paradigm_competition_no_findings_below_limit() -> None:
    findings = audit_paradigm_competition([])

    assert findings == []
