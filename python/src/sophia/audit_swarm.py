from __future__ import annotations


def audit_swarm(discoveries: list[dict]) -> list[dict]:
    findings = []

    if len(discoveries) == 0:
        findings.append(
            {
                "law": "discovery_stagnation",
                "severity": "watch",
                "semanticMode": "non-executive",
            }
        )

    return findings
