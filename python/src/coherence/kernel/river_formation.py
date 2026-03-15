"""River formation kernel."""

from __future__ import annotations

import numpy as np


def river_formation_step(state: dict, smoothing: float = 0.2) -> dict:
    """Apply lightweight coherence smoothing to emulate aligned flows."""
    psi = np.asarray(state["Psi"], dtype=float)
    smoothed = psi + smoothing * sum(np.gradient(g, axis=i) for i, g in enumerate(np.gradient(psi)))
    next_state = dict(state)
    next_state["Psi"] = smoothed
    return next_state
