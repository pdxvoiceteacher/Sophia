"""Advisory audit checks for embedding drift artifacts."""

from __future__ import annotations


def audit_embedding_drift(artifact: dict) -> list[dict]:
    findings = []

    for topic, data in artifact["drift"].items():
        if data["velocity_mean"] < 0.01:
            findings.append(
                {
                    "law": "topic_stagnation",
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": f"Topic {topic} shows low conceptual drift.",
                }
            )

        if data["velocity_max"] > 5.0:
            findings.append(
                {
                    "law": "topic_instability",
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": f"Topic {topic} shows extreme drift.",
                }
            )

    return findings
