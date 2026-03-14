"""Triadic Brain Evolution Engine.

This module orchestrates the entire knowledge dynamics pipeline.

It executes the triadic discovery loop:

corridor -> river -> terrace -> paradigm shift -> civilizational monitor
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone

from .civilizational_monitor import run_civilizational_monitor
from .corridor_detector import detect_discovery_corridors
from .hypothesis_generator import generate_hypotheses
from .hypothesis_testing import test_hypotheses
from .paradigm_shift_engine import detect_paradigm_shift
from .river_formation import river_formation_step
from .terrace_formation import terrace_formation_step
from .theory_formation import merge_theories


class EvolutionEngine:
    """Execute one full triadic-brain evolution cycle."""

    def __init__(self) -> None:
        self.step_index = 0
        self.telemetry: dict[str, list[dict]] = {}

    def _hash_state(self, state: dict) -> str:
        raw = json.dumps(state, sort_keys=True, default=_json_default).encode()
        return hashlib.sha256(raw).hexdigest()

    def run_step(self, state: dict) -> tuple[dict, dict]:
        state_hash_before = self._hash_state(state)

        corridors = detect_discovery_corridors(state)
        state = river_formation_step(state)
        state = terrace_formation_step(state)
        hypotheses = generate_hypotheses(corridors)
        results = test_hypotheses(hypotheses, state)
        theories = merge_theories(results)
        shifts = detect_paradigm_shift(theories)
        civ_state = run_civilizational_monitor(state)

        state_hash_after = self._hash_state(state)
        self.step_index += 1

        telemetry_record = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "step": self.step_index,
            "state_hash_before": state_hash_before,
            "state_hash_after": state_hash_after,
            "corridors": len(corridors),
            "hypotheses": len(hypotheses),
            "theories": len(theories),
            "paradigm_shifts": len(shifts),
            "civilizational_regime": civ_state["regime"],
        }

        self.telemetry.setdefault("steps", []).append(telemetry_record)
        return state, telemetry_record


def _json_default(value: object) -> object:
    import numpy as np

    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, np.generic):
        return value.item()
    raise TypeError(f"Object of type {type(value).__name__} is not JSON serializable")
