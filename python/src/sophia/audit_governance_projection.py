from __future__ import annotations


def audit_governance_projection(artifact: dict) -> list[dict]:
    findings = []

    for p in artifact["policies"]:
        if p["weight"] > 1.0:
            findings.append(
                {
                    "law": "policy_weight_excess",
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": "Governance weight unusually high.",
                }
            )

    return findings
