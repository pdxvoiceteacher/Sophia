from __future__ import annotations


def audit_homeostasis(artifact: dict) -> list[dict]:
    h_value = artifact["H"]

    findings = []

    if h_value < 0.4:
        findings.append(
            {
                "law": "epistemic_homeostasis",
                "severity": "warn",
                "advisory": "watch",
                "message": "Discovery collapse risk.",
            }
        )

    if h_value > 1.2:
        findings.append(
            {
                "law": "epistemic_homeostasis",
                "severity": "warn",
                "advisory": "watch",
                "message": "Exploration instability.",
            }
        )

    return findings
