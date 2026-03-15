from __future__ import annotations


def audit_corridor_confidence_calibrated(artifact: dict) -> list[dict]:
    findings = []

    for c in artifact.get("corridors", []):
        if c["confidence"] > 0.95:
            findings.append(
                {
                    "law": "overconfidence_risk",
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": "Confidence extremely high; verify calibration.",
                }
            )

    return findings
