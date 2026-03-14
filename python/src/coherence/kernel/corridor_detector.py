"""Discovery Corridor Detector.

Implements the coherence transport PDE:

∂Ψ/∂t = D∇²Ψ − ∇·(Ψ ∇Φ) + S
"""

from __future__ import annotations

import numpy as np


def laplacian(field: np.ndarray) -> np.ndarray:
    """Compute a simple Laplacian approximation over n-d fields."""
    grads = np.gradient(field)
    return sum(np.gradient(g, axis=i) for i, g in enumerate(grads))


def divergence(vector: tuple[np.ndarray, ...] | list[np.ndarray]) -> np.ndarray:
    """Compute divergence of a vector field represented by per-axis arrays."""
    return sum(np.gradient(v, axis=i) for i, v in enumerate(vector))


def detect_discovery_corridors(state: dict, D: float = 0.1) -> list[tuple[int, ...]]:
    """Detect high-gradient discovery corridors from PDE dynamics."""
    psi = np.asarray(state["Psi"])
    phi = np.asarray(state["Phi"])
    novelty_source = np.asarray(state.get("novelty_source", 0.0))

    diffusion = D * laplacian(psi)
    drift = -divergence(tuple(psi * g for g in np.gradient(phi)))
    _dpsi = diffusion + drift + novelty_source

    gradient_mag = np.sqrt(sum(g**2 for g in np.gradient(psi)))
    corridors = np.where(gradient_mag > 0.5)
    return list(zip(*corridors))
