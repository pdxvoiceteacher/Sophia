from __future__ import annotations


def audit_civilization_forecast(artifact: dict) -> list[dict]:
    findings = []

    timeline = artifact.get("timeline", [])

    if not timeline:
        return findings

    final = timeline[-1]["knowledge"]

    if final < timeline[0]["knowledge"]:
        findings.append(
            {
                "law": "civilizational_decay",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Knowledge forecast trends downward.",
            }
        )

    return findings
