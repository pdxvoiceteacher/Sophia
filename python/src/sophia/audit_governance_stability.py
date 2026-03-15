from __future__ import annotations


def audit_governance_stability(artifact: dict) -> list[dict]:
    findings = []

    regime = artifact.get("regime")

    if regime == "unstable_discovery":
        findings.append(
            {
                "law": "governance_instability_warning",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Discovery ecosystem becoming unstable.",
            }
        )

    if regime == "pre_capture_drift":
        findings.append(
            {
                "law": "capture_drift_warning",
                "severity": "warn",
                "semanticMode": "non-executive",
                "message": "Governance capture risk rising.",
            }
        )

    if regime == "systemic_instability":
        findings.append(
            {
                "law": "civilizational_instability",
                "severity": "docket",
                "semanticMode": "non-executive",
                "message": "Discovery ecosystem destabilized.",
            }
        )

    return findings
