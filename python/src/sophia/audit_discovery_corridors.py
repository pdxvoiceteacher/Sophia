"""Advisory audit checks for discovery corridor artifacts."""

from __future__ import annotations


def audit_discovery_corridors(artifact: dict) -> list[dict]:
    findings = []

    corridors = artifact.get("corridors", [])

    if len(corridors) == 0:
        findings.append(
            {
                "law": "discovery_corridor_absence",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "No discovery gradients detected in current Ψ field.",
            }
        )

    if len(corridors) > 100:
        findings.append(
            {
                "law": "corridor_noise_risk",
                "severity": "info",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Large number of corridors may indicate noise or fragmentation.",
            }
        )

    return findings
