"""Global Coherence Field Solver.

Computes the global coherence potential Φ(x)
and generates navigation maps across the lattice.
"""

from __future__ import annotations

import numpy as np


def compute_coherence_potential(state: dict, weights: dict) -> np.ndarray:
    """Compute weighted coherence potential field."""
    e = np.asarray(state["E"])
    t = np.asarray(state["T"])
    psi = np.asarray(state["Psi"])
    delta_s = np.asarray(state["DeltaS"])
    lambda_ = np.asarray(state["Lambda"])
    es = np.asarray(state["Es"])

    phi = (
        weights["psi"] * psi
        + weights["E"] * e
        + weights["T"] * t
        + weights["Es"] * es
        - weights["entropy"] * delta_s
        - weights["criticality"] * lambda_
    )
    return phi


def compute_gradient(field: np.ndarray) -> np.ndarray:
    """Return gradient magnitude map."""
    grad = np.gradient(field)
    return np.sqrt(sum(g**2 for g in grad))


def build_navigation_map(state: dict, weights: dict) -> dict:
    """Build serializable navigation artifact from coherence potential."""
    phi = compute_coherence_potential(state, weights)
    grad = compute_gradient(phi)
    return {
        "coherence_field": phi.tolist(),
        "gradient_magnitude": grad.tolist(),
        "max_gradient": float(np.max(grad)),
    }
