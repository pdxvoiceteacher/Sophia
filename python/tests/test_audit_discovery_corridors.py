from sophia.audit_discovery_corridors import audit_discovery_corridors


def test_no_discovery_corridors_detected():
    artifact = {"summary": {"corridorCount": 0}}

    findings = audit_discovery_corridors(artifact)

    assert findings == [
        {
            "severity": "info",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "No discovery corridors detected.",
        }
    ]
