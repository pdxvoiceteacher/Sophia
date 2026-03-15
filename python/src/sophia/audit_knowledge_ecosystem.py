from __future__ import annotations


def audit_knowledge_ecosystem(artifact: dict) -> list[dict]:
    findings = []

    if artifact["regime"] == "stagnation":
        findings.append(
            {
                "law": "knowledge_stagnation",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Knowledge ecosystem stagnating.",
            }
        )

    if artifact["regime"] == "fragmentation":
        findings.append(
            {
                "law": "knowledge_fragmentation",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Paradigm space fragmented.",
            }
        )

    return findings
