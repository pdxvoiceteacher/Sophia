from __future__ import annotations


class WeightRegistry:
    """Deterministic, pure in-memory weight lookup for Path B2 staging.

    This abstraction is simulation-only. It does not load files, registries,
    or dynamic sources.
    """

    def __init__(self, weights: dict[str, float] | None = None) -> None:
        self._weights = dict(weights or {})

    def get_weight(self, node_id: str) -> float:
        try:
            weight = float(self._weights.get(str(node_id), 1.0))
        except Exception:
            weight = 1.0
        if weight < 0.0:
            return 0.0
        return weight

    @classmethod
    def for_simulation(
        cls,
        *,
        node_ids: list[str],
        mode: str,
    ) -> "WeightRegistry":
        if mode == "linear":
            return cls({nid: float(i + 1) for i, nid in enumerate(node_ids)})
        if mode == "adversarial":
            high_count = max(1, len(node_ids) // 3)
            return cls({nid: (5.0 if i < high_count else 1.0) for i, nid in enumerate(node_ids)})
        return cls({nid: 1.0 for nid in node_ids})
