from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"

CONCEPT_PATH = BRIDGE_DIR / "concept_lattice_map.json"
CONSTELLATION_PATH = BRIDGE_DIR / "constellation_lattice_map.json"
ASSESSMENT_PATH = BRIDGE_DIR / "coherence_assessment.json"
RECOMMENDATIONS_PATH = BRIDGE_DIR / "sophia_recommendations.json"

ATTENTION_UPDATES_OUT = BRIDGE_DIR / "attention_updates.json"


@dataclass(slots=True)
class AttentionRuleResult:
    node_id: str
    previous_weight: float
    updated_weight: float
    delta: float
    rule: str
    explanation: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, value))


def _node_degree_weights(constellation_map: dict[str, Any]) -> dict[str, float]:
    edges = constellation_map.get("constellations")
    if not isinstance(edges, list) or not edges:
        return {}

    degree: dict[str, float] = {}
    for edge in edges:
        if not isinstance(edge, dict):
            continue
        weight = float(edge.get("weight", 1.0))
        src = edge.get("source")
        dst = edge.get("target")
        if isinstance(src, str):
            degree[src] = degree.get(src, 0.0) + weight
        if isinstance(dst, str):
            degree[dst] = degree.get(dst, 0.0) + weight

    if not degree:
        return {}

    max_deg = max(degree.values())
    return {k: (v / max_deg if max_deg > 0 else 0.0) for k, v in degree.items()}


def _rl_delta(*, base_weight: float, coherence: float, risk: float, regime: str, action: str, connectivity: float) -> tuple[float, str, str]:
    # Reward (coherence, connectivity) and penalty (risk) with small policy-step updates.
    reward = 0.60 * coherence + 0.40 * connectivity
    penalty = 0.75 * risk
    policy_signal = reward - penalty

    # Regime/action shaping terms act as policy rules.
    regime_shift = {
        "stable": 0.05,
        "watch": 0.00,
        "elevated": -0.05,
        "critical": -0.10,
    }.get(regime, 0.0)

    action_shift = {
        "reinforce": 0.07,
        "observe": 0.01,
        "attenuate": -0.05,
        "prune": -0.10,
    }.get(action, 0.0)

    alpha = 0.25
    delta = alpha * policy_signal + regime_shift + action_shift

    if action == "prune" and base_weight > 0.65:
        rule = "safety_prune_cap"
        delta -= 0.08
        explanation = "Critical pruning rule reduced high-attention branch to mitigate regime risk."
    elif action == "attenuate":
        rule = "risk_attenuation"
        explanation = "Risk-attenuation rule reduced attention in response to elevated instability/conflict."
    elif action == "reinforce":
        rule = "coherence_reinforcement"
        explanation = "Coherence reinforcement rule increased attention on convergent graph structure."
    else:
        rule = "observe_tracking"
        explanation = "Observation rule applied a minimal policy adjustment while collecting additional evidence."

    return delta, rule, explanation


def build_attention_updates() -> dict[str, Any]:
    concept_map = _load_json(CONCEPT_PATH)
    constellation_map = _load_json(CONSTELLATION_PATH)
    assessment = _load_json(ASSESSMENT_PATH)
    recommendations = _load_json(RECOMMENDATIONS_PATH)

    coherence = float(assessment.get("coherenceScore", 0.0))
    risk = float(assessment.get("riskScore", 1.0))
    regime = str(assessment.get("regimeClassification", "watch"))

    recs = recommendations.get("recommendations") if isinstance(recommendations, dict) else []
    action = "observe"
    if isinstance(recs, list) and recs and isinstance(recs[0], dict):
        action = str(recs[0].get("action") or "observe")

    connectivity = _node_degree_weights(constellation_map)
    concepts = concept_map.get("concepts")
    if not isinstance(concepts, list):
        concepts = []

    updates: list[dict[str, Any]] = []
    for item in concepts:
        if not isinstance(item, dict):
            continue
        node_id = str(item.get("id") or item.get("label") or "unknown")
        label = str(item.get("label") or node_id)

        base_weight = 0.45 + 0.35 * connectivity.get(node_id, 0.0)
        base_weight = _clamp01(base_weight)

        delta, rule, explanation = _rl_delta(
            base_weight=base_weight,
            coherence=coherence,
            risk=risk,
            regime=regime,
            action=action,
            connectivity=connectivity.get(node_id, 0.0),
        )
        new_weight = _clamp01(base_weight + delta)

        result = AttentionRuleResult(
            node_id=node_id,
            previous_weight=round(base_weight, 6),
            updated_weight=round(new_weight, 6),
            delta=round(new_weight - base_weight, 6),
            rule=rule,
            explanation=f"{explanation} Node '{label}' connectivity={connectivity.get(node_id, 0.0):.3f}.",
        )
        updates.append(
            {
                "node_id": result.node_id,
                "previous_weight": result.previous_weight,
                "updated_weight": result.updated_weight,
                "delta": result.delta,
                "rule": result.rule,
                "explanation": result.explanation,
            }
        )

    return {
        "schema": "attention_updates_v1",
        "created_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "inputs": {
            "concept_lattice_map": str(CONCEPT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "constellation_lattice_map": str(CONSTELLATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "coherence_assessment": str(ASSESSMENT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sophia_recommendations": str(RECOMMENDATIONS_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "policy": {
            "type": "reinforcement_learning_rules",
            "coherenceScore": coherence,
            "riskScore": risk,
            "regimeClassification": regime,
            "recommendedAction": action,
        },
        "updates": updates,
    }


def main() -> int:
    payload = build_attention_updates()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    ATTENTION_UPDATES_OUT.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {ATTENTION_UPDATES_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
