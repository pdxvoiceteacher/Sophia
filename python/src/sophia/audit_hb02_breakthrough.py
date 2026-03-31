"""Advisory audit checks for HB02 breakthrough prediction artifacts."""

from __future__ import annotations


def evaluate_breakthrough_prediction(timeline: list[dict], *, breakthrough_year: int) -> dict:
    predicted = any(
        point.get("year", breakthrough_year + 1) < breakthrough_year
        and float(point.get("corridor_score", 0.0)) >= 0.2
        for point in timeline
        if isinstance(point, dict)
    )

    return {
        "predicted": predicted,
        "breakthrough_year": breakthrough_year,
    }


def audit_hb02_breakthrough(artifact: dict) -> list[dict]:
    findings = []

    result = artifact["result"]

    if not result["predicted"]:
        findings.append(
            {
                "law": "dna_breakthrough_not_predicted",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "DNA corridor did not precede breakthrough.",
            }
        )

    return findings
