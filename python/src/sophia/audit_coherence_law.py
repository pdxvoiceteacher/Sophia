"""General coherence-law advisory audit checks."""

from __future__ import annotations


def audit_coherence_law(result: dict) -> list[dict]:
    findings = []

    psi = result.get("score", 0)
    delta_s = result.get("deltaS", 1)

    if delta_s > psi:
        findings.append(
            {
                "law": "fragmentation_noise",
                "message": f"ΔS ({delta_s:.3f}) > Ψ ({psi:.3f}) → fragmentation regime",
                "severity": "watch",
            }
        )

    if psi > 0.5 and delta_s < 0.5:
        findings.append(
            {
                "law": "coherence_growth",
                "message": "Coherence exceeding entropy → possible corridor",
                "severity": "info",
            }
        )

    return findings
