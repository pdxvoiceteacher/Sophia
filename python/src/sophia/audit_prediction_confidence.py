"""Advisory audit checks for universal prediction confidence signals."""

from __future__ import annotations


def audit_prediction_confidence(artifact: dict) -> list[dict]:
    findings = []

    for c in artifact["confidences"]:
        prob = c["probability"]

        if prob < 0.2:
            findings.append(
                {
                    "law": "low_breakthrough_probability",
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": "Discovery corridor probability below expected threshold.",
                }
            )

        if prob > 0.95:
            findings.append(
                {
                    "law": "prediction_overconfidence",
                    "severity": "watch",
                    "semanticMode": "non-executive",
                    "message": "Prediction probability unusually high; check calibration.",
                }
            )

    return findings
