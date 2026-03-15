from __future__ import annotations


def audit_paradigm_competition(terraces: list[dict]) -> list[dict]:
    findings = []

    if len(terraces) > 5:
        findings.append(
            {
                "law": "paradigm_fragmentation",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Too many competing terraces detected.",
            }
        )

    return findings
