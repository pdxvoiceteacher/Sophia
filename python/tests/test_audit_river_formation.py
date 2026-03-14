from sophia.audit_river_formation import audit_river_formation


def test_river_saturation_warning():
    artifact = {
        "summary": {
            "max_river_after": 0.99,
            "max_gradient_sq": 0.4,
            "river_total_before": 0.2,
            "river_total_after": 1.8,
        }
    }

    findings = audit_river_formation(artifact)
    assert findings
    assert findings[0]["semanticMode"] == "non-executive"
