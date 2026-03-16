from __future__ import annotations


def audit_triadic_diagnostics(artifact: dict) -> list[dict]:
    findings = []

    if artifact.get("semanticMode") != "non-executive":
        findings.append(
            {
                "law": "semantic_mode_violation",
                "severity": "warn",
                "semanticMode": "non-executive",
                "message": "Diagnostics artifact must remain non-executive.",
            }
        )

    if artifact.get("system_status") != "stable":
        findings.append(
            {
                "law": "system_instability",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Diagnostics indicate non-stable system status.",
            }
        )

    category_map = {
        "kernel_health": "kernel_health_alerts",
        "governance_health": "governance_health_alerts",
        "epistemic_health": "epistemic_health_alerts",
    }
    for key, law in category_map.items():
        issues = artifact.get(key, [])
        if len(issues) > 0:
            findings.append(
                {
                    "law": law,
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": f"{key} contains {len(issues)} issue(s).",
                }
            )

    return findings
