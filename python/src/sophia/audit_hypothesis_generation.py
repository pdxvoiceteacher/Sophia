"""Advisory audit checks for hypothesis generation artifacts."""

from __future__ import annotations


def audit_hypothesis_generation(artifact: dict) -> list[dict]:
    findings = []

    hypotheses = artifact.get("hypotheses", [])

    if len(hypotheses) == 0:
        findings.append(
            {
                "law": "hypothesis_generation_stall",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "No hypotheses generated from corridor vectors.",
            }
        )

    if len(hypotheses) > 50:
        findings.append(
            {
                "law": "hypothesis_overproduction",
                "severity": "info",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Hypothesis volume high; filtering may be required.",
            }
        )

    return findings
