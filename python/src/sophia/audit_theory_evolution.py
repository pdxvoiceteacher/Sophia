from __future__ import annotations


def audit_theory_evolution(artifact: dict) -> list[dict]:
    findings = []

    if not artifact["theories"]:
        findings.append(
            {
                "law": "theory_ecosystem_extinction",
                "severity": "warn",
                "semanticMode": "non-executive",
                "message": "No theories remain in evolutionary pool.",
            }
        )

    return findings
