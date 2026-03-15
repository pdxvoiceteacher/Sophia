from __future__ import annotations


def audit_swarm_discovery(artifact: dict) -> list[dict]:
    findings = []

    if len(artifact.get("discoveries", [])) == 0:
        findings.append(
            {
                "law": "swarm_stagnation",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Swarm produced no discoveries.",
            }
        )

    return findings
