"""Advisory audit checks for coherence quality in sonified outputs."""

from __future__ import annotations


def audit_audio_coherence(metrics: dict) -> list[dict]:
    findings = []

    psi = metrics.get("phi_total", 0)

    if psi < 0.2:
        findings.append(
            {
                "law": "audio_coherence_low",
                "severity": "watch",
                "semanticMode": "non-executive",
            }
        )

    if psi > 0.8:
        findings.append(
            {
                "law": "audio_high_coherence_peak",
                "severity": "info",
                "semanticMode": "non-executive",
            }
        )

    return findings
