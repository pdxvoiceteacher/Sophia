from sophia.audit_coherence_gradient_map import audit_coherence_gradient_map


def test_audit_coherence_gradient_map_no_strong_gradients_info():
    artifact = {
        "nodes": [
            {"gradientMagnitude": 0.1},
            {"gradientMagnitude": 0.5},
        ]
    }

    findings = audit_coherence_gradient_map(artifact)

    assert findings == [
        {
            "severity": "info",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "No strong coherence gradients currently support corridor emergence.",
            "law": "discovery_gradient_support",
        }
    ]
