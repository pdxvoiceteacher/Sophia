from sophia.audit_civilizational_coherence import audit_civilizational_coherence


def test_audit_orthodoxy_collapse():
    artifact = {
        "metrics": {"S_civ": 0.42},
        "summary": {"regime": "orthodoxy_collapse"},
    }
    findings = audit_civilizational_coherence(artifact)
    assert findings
    assert findings[0]["semanticMode"] == "non-executive"


def test_audit_accepts_top_level_scalar_shape() -> None:
    findings = audit_civilizational_coherence({"S_civ": 0.95})
    assert findings
    assert findings[0]["law"] == "civilizational_stability_threshold"


def test_audit_derives_fragmentation_regime_when_scalar_low() -> None:
    findings = audit_civilizational_coherence({"S_civ": 0.5})
    assert findings
    assert findings[0]["law"] == "fragmentation_noise"
