from sophia.audit_swarm import audit_swarm


def test_audit_swarm_flags_discovery_stagnation_when_empty() -> None:
    findings = audit_swarm([])

    assert findings == [
        {
            "law": "discovery_stagnation",
            "severity": "watch",
            "semanticMode": "non-executive",
        }
    ]


def test_audit_swarm_no_findings_when_discoveries_present() -> None:
    findings = audit_swarm([{"id": "d1"}])

    assert findings == []
