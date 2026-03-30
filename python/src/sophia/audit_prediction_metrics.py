"""Advisory audit checks for universal prediction metrics."""

from __future__ import annotations


def audit_prediction_metrics(artifact: dict) -> list[dict]:
    findings = []

    metrics = artifact["metrics"]

    precision = metrics["precision"]
    recall = metrics["recall"]
    fpr = metrics["false_positive_rate"]

    if precision < 0.5:
        findings.append(
            {
                "law": "prediction_precision_low",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Prediction precision below acceptable threshold.",
            }
        )

    if recall < 0.5:
        findings.append(
            {
                "law": "prediction_recall_low",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Recall indicates missed discoveries.",
            }
        )

    if fpr > 0.5:
        findings.append(
            {
                "law": "false_positive_rate_high",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Prediction system generating excessive false positives.",
            }
        )

    return findings
