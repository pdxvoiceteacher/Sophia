from __future__ import annotations


def audit_cultural_transmission(artifact: dict) -> list[dict]:
    findings = []

    metrics = artifact.get("metrics", {})

    if metrics.get("understanding", 0) < 0.2:
        findings.append(
            {
                "law": "low_public_understanding",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Theory adoption limited by low public comprehension.",
            }
        )

    return findings
