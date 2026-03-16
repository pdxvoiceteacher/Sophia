from __future__ import annotations


def audit_governance_phase_diagram(artifact: dict) -> list[dict]:
    findings = []

    surface = artifact.get("surface", [])

    rupture_points = [p for p in surface if p["regime"] == "civilizational_rupture"]

    if len(rupture_points) > 0:
        findings.append(
            {
                "law": "governance_instability_region",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Phase diagram contains civilizational rupture regions.",
            }
        )

    return findings
