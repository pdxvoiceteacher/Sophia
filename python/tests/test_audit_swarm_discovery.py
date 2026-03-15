from sophia.audit_swarm_discovery import audit_swarm_discovery


def test_audit_swarm_discovery_emits_stagnation_finding_when_empty() -> None:
    findings = audit_swarm_discovery({"discoveries": []})

    assert findings == [
        {
            "law": "swarm_stagnation",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Swarm produced no discoveries.",
        }
    ]


def test_audit_swarm_discovery_no_findings_when_discoveries_present() -> None:
    findings = audit_swarm_discovery({"discoveries": [{"id": "d1"}]})

    assert findings == []


def test_audit_swarm_discovery_defaults_to_stagnation_when_key_missing() -> None:
    findings = audit_swarm_discovery({})

    assert findings == [
        {
            "law": "swarm_stagnation",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Swarm produced no discoveries.",
        }
    ]
