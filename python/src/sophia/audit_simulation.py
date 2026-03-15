from __future__ import annotations


def audit_simulation(state: dict) -> list[dict]:
    findings = []

    scalar = float(state.get("S_civ", 0.0))
    if scalar < 0.2:
        findings.append(
            {
                "law": "civilization_collapse_risk",
                "severity": "warn",
                "semanticMode": "non-executive",
            }
        )

    return findings
