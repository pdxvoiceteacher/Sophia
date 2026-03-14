from __future__ import annotations


def audit_global_coherence_field(artifact: dict) -> list[dict]:
    findings = []

    summary = artifact.get("summary", {})
    max_grad = float(summary.get("maxGradientMagnitude", 0.0))

    if max_grad < 1e-6:
        findings.append({
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Global coherence field is effectively flat; no strong navigation gradients detected.",
            "law": "coherence_gradient_flatness",
        })

    return findings
