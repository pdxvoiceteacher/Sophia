"""Advisory audit checks for paradigm-shift events."""

from __future__ import annotations


def audit_paradigm_shift(event: dict) -> list[dict]:
    findings = []

    if event.get("event") == "paradigm_shift":
        findings.append(
            {
                "law": "paradigm_shift_detected",
                "severity": "warn",
                "advisory": "docket",
                "semanticMode": "non-executive",
                "message": "Terrace collapse detected; knowledge field entering rupture phase.",
            }
        )

    if event.get("new_corridors") == 0:
        findings.append(
            {
                "law": "rupture_without_corridors",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Rupture detected but no new corridors formed.",
            }
        )

    return findings
