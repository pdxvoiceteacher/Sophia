from __future__ import annotations


def audit_simulation(state: dict) -> list[dict]:
    findings = []

    if state["S_civ"] < 0.2:
        findings.append(
            {
                "law": "civilization_collapse_risk",
                "severity": "warn",
                "semanticMode": "non-executive",
            }
        )

    return findings
