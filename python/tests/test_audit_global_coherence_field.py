from sophia.audit_global_coherence_field import audit_global_coherence_field


def test_audit_global_coherence_field_flat_gradient_watch():
    artifact = {"summary": {"maxGradientMagnitude": 0.0}}

    findings = audit_global_coherence_field(artifact)

    assert findings == [
        {
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Global coherence field is effectively flat; no strong navigation gradients detected.",
            "law": "coherence_gradient_flatness",
        }
    ]
