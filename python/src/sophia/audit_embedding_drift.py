"""Advisory audit checks for embedding drift artifacts."""

from __future__ import annotations


def audit_embedding_drift(artifact: dict) -> list[dict]:
    findings = []

    if not artifact.get("velocities"):
        findings.append(
            {
                "law": "embedding_drift_missing",
                "severity": "watch",
                "semanticMode": "non-executive",
            }
        )

    return findings
