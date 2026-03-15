"""Renormalization utilities for multi-scale knowledge-field dynamics."""

from __future__ import annotations

import numpy as np


def coarse_grain(field: np.ndarray | list[float], scale: int) -> np.ndarray:
    """Average contiguous blocks to produce a coarse-grained 1D field."""
    if scale <= 0:
        raise ValueError("scale must be positive")

    values = np.asarray(field, dtype=float)
    if values.ndim != 1:
        raise ValueError("field must be one-dimensional")
    if values.size == 0:
        raise ValueError("field must be non-empty")

    n_blocks = values.size // scale
    if n_blocks == 0:
        raise ValueError("scale cannot exceed field length")

    trimmed = values[: n_blocks * scale]
    return np.mean(trimmed.reshape(n_blocks, scale), axis=1)


def renormalize(field: np.ndarray | list[float], scale: int) -> np.ndarray:
    """Coarse-grain a field and normalize amplitudes to unit peak magnitude."""
    coarse = coarse_grain(field, scale)
    peak = np.max(np.abs(coarse))
    if peak == 0:
        return coarse
    return coarse / peak
