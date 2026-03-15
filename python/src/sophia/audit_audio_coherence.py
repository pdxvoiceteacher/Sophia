"""Advisory audit checks for audio coherence streams."""

from __future__ import annotations


def audit_audio_coherence(midi_stream: dict) -> list[dict]:
    findings = []

    pitch_variance = midi_stream.get("pitch_variance", 0.0)

    if pitch_variance > 24:
        findings.append(
            {
                "law": "audio_entropy_excess",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Audio pitch variance indicates elevated entropy in sonified coherence signals.",
            }
        )

    return findings
