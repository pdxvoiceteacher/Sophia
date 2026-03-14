from __future__ import annotations


def audit_river_formation(artifact: dict) -> list[dict]:
    """
    Advisory-only audit for river formation artifacts.
    """
    findings = []

    summary = artifact.get("summary", {})
    max_river = float(summary.get("max_river_after", 0.0))
    max_grad = float(summary.get("max_gradient_sq", 0.0))
    total_before = float(summary.get("river_total_before", 0.0))
    total_after = float(summary.get("river_total_after", 0.0))

    if max_grad < 1e-6:
        findings.append({
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "River phase shows negligible corridor-gradient reinforcement.",
            "law": "river_gradient_support",
        })

    if max_river > 0.95:
        findings.append({
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "River density approaching saturation; inspect for over-concentration.",
            "law": "river_saturation_risk",
        })

    if total_after < total_before and max_grad > 0.05:
        findings.append({
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "River structure decayed despite strong gradients; inspect beta/transport balance.",
            "law": "river_decay_mismatch",
        })

    return findings
