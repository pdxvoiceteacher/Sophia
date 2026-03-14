from sophia.audit_civilizational_coherence import audit_civilizational_coherence


def test_audit_orthodoxy_collapse():
    artifact = {
        "metrics": {"S_civ": 0.42},
        "summary": {"regime": "orthodoxy_collapse"},
    }
    findings = audit_civilizational_coherence(artifact)
    assert findings
    assert findings[0]["semanticMode"] == "non-executive"
