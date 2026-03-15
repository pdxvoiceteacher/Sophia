"""Advisory audit checks for theory-formation artifacts."""

from __future__ import annotations


def audit_theory_formation(artifact: dict) -> list[dict]:
    findings = []

    theories = artifact.get("theories", [])

    if len(theories) == 0:
        findings.append(
            {
                "law": "theory_formation_absent",
                "severity": "info",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "No theories formed from tested hypotheses.",
            }
        )

    if len(theories) > 10:
        findings.append(
            {
                "law": "theory_fragmentation_risk",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Large number of theories may indicate lack of convergence.",
            }
        )

    return findings


def audit_theories(artifact: dict) -> list[dict]:
    """Backward-compatible alias for older call sites."""
    return audit_theory_formation(artifact)
