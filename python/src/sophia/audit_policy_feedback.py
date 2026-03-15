from __future__ import annotations


def audit_policy_feedback(artifact: dict) -> list[dict]:
    findings = []

    pressure = artifact["policy_pressure"]

    if max(pressure) > 1.5:
        findings.append(
            {
                "law": "policy_overbias",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Policy pressure may excessively bias discovery.",
            }
        )

    return findings
