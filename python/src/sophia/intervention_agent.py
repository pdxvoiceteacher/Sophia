from __future__ import annotations

from typing import Any, Dict


def sophia_intervention_agent(state: Dict[str, Any]) -> Dict[str, Any]:
    """
    Sophia proposes interventions based on audit + metrics.
    """

    entropy = state.get("entropy_extension", {})
    ethics = state.get("field_ethics", {})

    external_entropy = entropy.get("external_entropy", 0.0)
    empathy = ethics.get("empathy", 0.5)

    # RULES (will evolve into learned policy)
    if external_entropy > 0.1:
        return {
            "action": "reduce_entropy",
            "priority": "high",
            "reason": "external_entropy_exceeds_threshold",
        }

    if empathy < 0.5:
        return {
            "action": "increase_empathy_weight",
            "priority": "medium",
            "reason": "low_empathy_detected",
        }

    return {
        "action": "maintain_state",
        "priority": "low",
    }
