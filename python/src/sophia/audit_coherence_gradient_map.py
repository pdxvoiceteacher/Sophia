from __future__ import annotations


def audit_coherence_gradient_map(artifact: dict) -> list[dict]:
    findings = []

    nodes = artifact.get("nodes", [])
    strong = [n for n in nodes if float(n.get("gradientMagnitude", 0.0)) > 0.5]

    if len(strong) == 0:
        findings.append({
            "severity": "info",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "No strong coherence gradients currently support corridor emergence.",
            "law": "discovery_gradient_support",
        })

    return findings
