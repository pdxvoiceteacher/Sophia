"""Advisory audit checks for entropy drift artifacts."""

from __future__ import annotations


def audit_entropy_drift(artifact: dict) -> list[dict]:
    findings = []

    entropy_rate = artifact.get("entropy_rate", 0.0)

    if entropy_rate > 0.5:
        findings.append(
            {
                "law": "entropy_excess",
                "severity": "warn",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Entropy drift exceeds the safe monitoring threshold.",
            }
        )

    return findings
