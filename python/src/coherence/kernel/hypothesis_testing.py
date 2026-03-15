"""Hypothesis testing kernel."""

from __future__ import annotations

import numpy as np


def test_hypotheses(hypotheses: list[dict], state: dict) -> list[dict]:
    """Score hypotheses against current field state."""
    psi = np.asarray(state["Psi"], dtype=float)
    mean_score = float(np.mean(np.abs(psi))) if psi.size else 0.0
    return [{**h, "score": mean_score} for h in hypotheses]
