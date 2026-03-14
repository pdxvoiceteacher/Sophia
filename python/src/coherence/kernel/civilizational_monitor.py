"""Civilizational monitor kernel."""

from __future__ import annotations

import numpy as np


def run_civilizational_monitor(state: dict) -> dict:
    """Compute a minimal regime classification from coherence magnitude."""
    psi = np.asarray(state["Psi"], dtype=float)
    score = float(np.mean(np.abs(psi))) if psi.size else 0.0
    regime = "healthy_discovery" if score >= 0.1 else "fragmentation"
    return {"score": score, "regime": regime}
