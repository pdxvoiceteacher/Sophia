from __future__ import annotations


def audit_anti_capture(artifact: dict) -> list[dict]:
    findings = []

    risk = artifact.get("risk_score", 0)
    regime = artifact.get("regime")

    if regime == "capture_risk":
        findings.append(
            {
                "law": "capture_risk_detected",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Governance capture risk rising.",
            }
        )

    if regime == "oligarchic_drift":
        findings.append(
            {
                "law": "oligarchic_drift_warning",
                "severity": "warn",
                "semanticMode": "non-executive",
                "message": "Power concentration and transparency decline detected.",
            }
        )

    if regime == "systemic_capture":
        findings.append(
            {
                "law": "systemic_capture_detected",
                "severity": "docket",
                "semanticMode": "non-executive",
                "message": "System approaching full capture dynamics.",
            }
        )

    return findings
