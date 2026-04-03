from __future__ import annotations

from sophia.audit_hb02_breakthrough import evaluate_breakthrough_prediction


def test_hb02_breakthrough() -> None:
    timeline = [
        {"year": 1947, "corridor_score": 0.1},
        {"year": 1948, "corridor_score": 0.15},
        {"year": 1949, "corridor_score": 0.25},
        {"year": 1950, "corridor_score": 0.42},
        {"year": 1951, "corridor_score": 0.5},
    ]

    result = evaluate_breakthrough_prediction(
        timeline,
        breakthrough_year=1953,
    )

    assert result["predicted"] is True
