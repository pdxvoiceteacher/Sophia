"""Terrace formation kernel."""

from __future__ import annotations

import numpy as np


def terrace_formation_step(state: dict, threshold: float = 0.05) -> dict:
    """Quantize low-amplitude updates into stable terraces."""
    psi = np.asarray(state["Psi"], dtype=float)
    terraced = np.where(np.abs(psi) < threshold, 0.0, psi)
    next_state = dict(state)
    next_state["Psi"] = terraced
    return next_state
