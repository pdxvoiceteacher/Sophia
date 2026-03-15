"""Advisory audit checks for entropy-to-audio signal mapping."""

from __future__ import annotations


def audit_entropy_audio_signal(artifact: dict) -> list[dict]:
    findings = []

    chromatic_ratio = artifact.get("chromatic_ratio", 0.0)
    entropy_rate = artifact.get("entropy_rate", 0.0)

    if chromatic_ratio > 0.4 and entropy_rate > 0.5:
        findings.append(
            {
                "law": "entropy_audio_signal_saturation",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Entropy sonification saturation detected; chromatic tension may obscure coherent motifs.",
            }
        )

    return findings
