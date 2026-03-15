"""Advisory audit checks for free-energy artifacts."""

from __future__ import annotations


def audit_free_energy(artifact: dict) -> list[dict]:
    findings = []

    free_energy = artifact.get("free_energy")
    previous_free_energy = artifact.get("previous_free_energy")

    if free_energy is None:
        findings.append(
            {
                "law": "free_energy_missing",
                "severity": "info",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Free-energy value missing from artifact.",
            }
        )
        return findings

    if previous_free_energy is not None and free_energy > previous_free_energy:
        findings.append(
            {
                "law": "free_energy_increase",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Free energy increased; stabilization trend may be reversing.",
            }
        )

    return findings
