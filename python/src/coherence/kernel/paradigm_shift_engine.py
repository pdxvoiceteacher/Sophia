"""Paradigm shift detection kernel."""

from __future__ import annotations


def detect_paradigm_shift(theories: list[dict], shift_threshold: int = 10) -> list[dict]:
    """Emit advisory shift signals when theory volume is high."""
    if len(theories) >= shift_threshold:
        return [{"type": "theory-density-shift", "count": len(theories)}]
    return []
