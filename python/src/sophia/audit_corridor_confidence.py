from __future__ import annotations


def audit_corridor_confidence(artifact: dict) -> list[dict]:
    findings = []

    for c in artifact.get("corridors", []):
        if c["confidence"] < 0.2:
            findings.append(
                {
                    "law": "weak_discovery_signal",
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": f"Low confidence corridor for {c['topic']}",
                }
            )

    return findings
