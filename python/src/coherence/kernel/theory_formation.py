"""Theory formation kernel."""

from __future__ import annotations


def merge_theories(results: list[dict], score_threshold: float = 0.0) -> list[dict]:
    """Merge tested hypotheses into provisional theories."""
    theories = [r for r in results if r.get("score", 0.0) >= score_threshold]
    for idx, theory in enumerate(theories):
        theory.setdefault("theory_id", f"T-{idx:04d}")
    return theories
