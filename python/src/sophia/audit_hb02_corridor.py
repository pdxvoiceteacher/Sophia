"""Advisory audit checks for HB02 corridor artifacts."""

from __future__ import annotations


def audit_hb02_corridor(artifact: dict) -> list[dict]:
    findings = []

    score = artifact["metrics"]["corridor_score"]

    if score < 0.2:
        findings.append(
            {
                "law": "dna_corridor_not_detected",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "DNA discovery corridor signal weak.",
            }
        )

    return findings
