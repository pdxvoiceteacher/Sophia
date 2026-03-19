"""Advisory audit checks for corridor signal validity."""

from __future__ import annotations


def audit_corridor_validity(result: dict) -> list[dict]:
    findings = []

    slope = result.get("slope", 0)

    if abs(slope) < 1e-6:
        findings.append(
            {
                "law": "no_signal_detected",
                "severity": "warn",
                "message": "No measurable cross-domain convergence.",
                "semanticMode": "non-executive",
            }
        )

    if result.get("score", 0) > 0.95:
        findings.append(
            {
                "law": "possible_metric_saturation",
                "severity": "watch",
                "message": "Score extremely high — check for metric inflation.",
                "semanticMode": "non-executive",
            }
        )

    return findings
