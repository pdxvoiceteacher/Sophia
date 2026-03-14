"""Audit the triadic brain evolution loop."""

from __future__ import annotations


def audit_evolution_step(record: dict) -> list[dict]:
    findings = []

    if record["hypotheses"] == 0:
        findings.append(
            {
                "law": "discovery_stagnation",
                "severity": "watch",
                "message": "No hypotheses generated this step",
                "semanticMode": "non-executive",
            }
        )

    if record["civilizational_regime"] == "fragmentation":
        findings.append(
            {
                "law": "civilizational_fragmentation",
                "severity": "warn",
                "message": "Knowledge ecosystem fragmentation detected",
                "semanticMode": "non-executive",
            }
        )

    return findings
