from __future__ import annotations


def audit_civilization(artifact: dict) -> list[dict]:
    findings = []

    psi = artifact["psi_vector"]

    if max(psi) - min(psi) > 0.8:
        findings.append(
            {
                "law": "civilizational_instability",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Large divergence between knowledge domains.",
            }
        )

    return findings
