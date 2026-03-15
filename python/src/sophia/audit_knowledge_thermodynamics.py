"""Advisory audit checks for knowledge thermodynamics artifacts."""

from __future__ import annotations


def audit_knowledge_thermodynamics(artifact: dict) -> list[dict]:
    findings = []

    knowledge_energy = artifact.get("knowledge_energy")
    power_in = artifact.get("power_in")
    power_diss = artifact.get("power_diss")

    if knowledge_energy is None:
        findings.append(
            {
                "law": "knowledge_energy_missing",
                "severity": "info",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Knowledge energy functional is missing from artifact.",
            }
        )

    if power_in is not None and power_diss is not None and power_diss > power_in:
        findings.append(
            {
                "law": "dissipation_dominance",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Dissipation exceeds novelty injection; discovery capacity may contract.",
            }
        )

    return findings
