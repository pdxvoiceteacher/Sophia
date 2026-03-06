from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

CONCEPT_PATH = BRIDGE_DIR / "concept_lattice_map.json"
CONSTELLATION_PATH = BRIDGE_DIR / "constellation_lattice_map.json"
REGIME_PATH = BRIDGE_DIR / "publication_regime_map.json"
ASSESSMENT_PATH = BRIDGE_DIR / "coherence_assessment.json"
RECOMMENDATIONS_PATH = BRIDGE_DIR / "sophia_recommendations.json"
DRIFT_PATH = BRIDGE_DIR / "coherence_drift_map.json"

ATTENTION_UPDATES_OUT = BRIDGE_DIR / "attention_updates.json"
ATTENTION_SUMMARY_OUT = BRIDGE_DIR / "attention_update_summary.json"

ATTENTION_SCHEMA_PATH = SCHEMA_DIR / "attention_updates_v1.schema.json"


@dataclass(slots=True)
class AttentionRuleResult:
    target_id: str
    previous_weight: float
    updated_weight: float
    delta: float
    coherence_score: float
    risk_score: float
    drift_score: float
    governing_rule: str
    explanation: str



def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


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


def _node_drift_scores(drift_map: dict[str, Any]) -> dict[str, float]:
    scores: dict[str, float] = {}

    node_items = drift_map.get("nodes")
    if isinstance(node_items, list):
        for item in node_items:
            if not isinstance(item, dict):
                continue
            node_id = item.get("id") or item.get("targetId") or item.get("node_id")
            drift = item.get("driftScore")
            if isinstance(node_id, str) and isinstance(drift, (int, float)):
                scores[node_id] = _clamp01(drift)

    map_items = drift_map.get("driftByNode")
    if isinstance(map_items, dict):
        for node_id, drift in map_items.items():
            if isinstance(node_id, str) and isinstance(drift, (int, float)):
                scores[node_id] = _clamp01(drift)

    return scores


def _resolve_created_at(assessment: dict[str, Any], regime_map: dict[str, Any], drift_map: dict[str, Any]) -> str:
    for source in (assessment, regime_map, drift_map):
        ts = source.get("created_at") if isinstance(source, dict) else None
        if isinstance(ts, str) and ts:
            return ts
    return "1970-01-01T00:00:00Z"


def _rl_delta(
    *,
    base_weight: float,
    coherence: float,
    risk: float,
    drift: float,
    regime: str,
    action: str,
    connectivity: float,
) -> tuple[float, str, str]:
    # CoherenceLattice truth -> Sophia evaluation -> Publisher overlay
    reward = 0.50 * coherence + 0.25 * connectivity + 0.15 * (1.0 - drift)
    penalty = 0.65 * risk + 0.35 * drift
    policy_signal = reward - penalty

    regime_shift = {
        "stable": 0.04,
        "watch": 0.00,
        "elevated": -0.04,
        "critical": -0.09,
    }.get(regime, 0.0)

    action_shift = {
        "reinforce": 0.06,
        "observe": 0.00,
        "attenuate": -0.05,
        "prune": -0.10,
    }.get(action, 0.0)

    drift_shift = -0.12 * drift
    alpha = 0.22
    delta = alpha * policy_signal + regime_shift + action_shift + drift_shift

    if drift >= 0.75:
        rule = "formal_drift_guard"
        delta -= 0.08
        explanation = "Formal drift guard applied because coherence_drift_map indicates high drift risk."
    elif action == "prune" and base_weight > 0.60:
        rule = "safety_prune_cap"
        delta -= 0.05
        explanation = "Prune policy capped high-weight branches under critical governance risk."
    elif action == "attenuate":
        rule = "risk_attenuation"
        explanation = "Attenuation rule reduced attention where regime and drift indicate instability."
    elif action == "reinforce" and drift <= 0.25:
        rule = "coherence_reinforcement"
        explanation = "Reinforcement rule increased attention on low-drift, high-coherence targets."
    else:
        rule = "observe_tracking"
        explanation = "Observation rule kept moderate adaptation while awaiting stronger drift/coherence signal."

    return delta, rule, explanation


def _validate_against_schema(payload: dict[str, Any], schema_path: Path) -> None:
    schema = _load_json(schema_path)
    Draft202012Validator(schema).validate(payload)


def build_attention_updates() -> tuple[dict[str, Any], dict[str, Any]]:
    concept_map = _load_json(CONCEPT_PATH)
    constellation_map = _load_json(CONSTELLATION_PATH)
    regime_map = _load_json(REGIME_PATH)
    assessment = _load_json(ASSESSMENT_PATH)
    recommendations = _load_json(RECOMMENDATIONS_PATH)
    drift_map = _load_json(DRIFT_PATH)

    coherence = float(assessment.get("coherenceScore", 0.0))
    risk = float(assessment.get("riskScore", 1.0))
    regime = str(assessment.get("regimeClassification", regime_map.get("regime", "watch")))

    recs = recommendations.get("recommendations") if isinstance(recommendations, dict) else []
    action = "observe"
    if isinstance(recs, list) and recs and isinstance(recs[0], dict):
        action = str(recs[0].get("action") or "observe")

    connectivity = _node_degree_weights(constellation_map)
    drift_scores = _node_drift_scores(drift_map)

    concepts = concept_map.get("concepts")
    if not isinstance(concepts, list):
        concepts = []

    updates: list[dict[str, Any]] = []
    for item in concepts:
        if not isinstance(item, dict):
            continue
        node_id = str(item.get("id") or item.get("label") or "unknown")
        label = str(item.get("label") or node_id)

        base_weight = _clamp01(0.45 + 0.35 * connectivity.get(node_id, 0.0))
        drift = _clamp01(drift_scores.get(node_id, drift_map.get("globalDriftScore", 0.0)))

        delta, rule, explanation = _rl_delta(
            base_weight=base_weight,
            coherence=coherence,
            risk=risk,
            drift=drift,
            regime=regime,
            action=action,
            connectivity=connectivity.get(node_id, 0.0),
        )
        new_weight = _clamp01(base_weight + delta)

        result = AttentionRuleResult(
            target_id=node_id,
            previous_weight=round(base_weight, 6),
            updated_weight=round(new_weight, 6),
            delta=round(new_weight - base_weight, 6),
            coherence_score=round(coherence, 6),
            risk_score=round(risk, 6),
            drift_score=round(drift, 6),
            governing_rule=rule,
            explanation=(
                f"{explanation} target='{label}', connectivity={connectivity.get(node_id, 0.0):.3f}, "
                f"coherence={coherence:.3f}, risk={risk:.3f}, drift={drift:.3f}."
            ),
        )
        updates.append(
            {
                "targetId": result.target_id,
                "previous_weight": result.previous_weight,
                "updated_weight": result.updated_weight,
                "delta": result.delta,
                "coherenceScore": result.coherence_score,
                "riskScore": result.risk_score,
                "driftScore": result.drift_score,
                "governing_rule": result.governing_rule,
                "explanation": result.explanation,
            }
        )

    updates = sorted(updates, key=lambda x: x["targetId"])
    created_at = _resolve_created_at(assessment, regime_map, drift_map)

    payload = {
        "schema": "attention_updates_v1",
        "created_at": created_at,
        "pipeline": "CoherenceLattice truth -> Sophia evaluation -> Publisher overlay",
        "artifactSemantics": {
            "formal_drift": "CoherenceLattice truth",
            "attention_update": "Sophia executive interpretation",
            "overlay_rendering": "Publisher visualization/memory presentation",
        },
        "inputs": {
            "concept_lattice_map": str(CONCEPT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "constellation_lattice_map": str(CONSTELLATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "publication_regime_map": str(REGIME_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "coherence_assessment": str(ASSESSMENT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sophia_recommendations": str(RECOMMENDATIONS_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "coherence_drift_map": str(DRIFT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "policy": {
            "type": "reinforcement_learning_rules",
            "coherenceScore": round(coherence, 6),
            "riskScore": round(risk, 6),
            "regimeClassification": regime,
            "recommendedAction": action,
            "formalDriftSignal": round(_clamp01(float(drift_map.get("globalDriftScore", 0.0))), 6),
        },
        "updates": updates,
    }

    reinforced = [u for u in updates if u["delta"] > 0]
    attenuated = [u for u in updates if u["delta"] < 0]
    top_priority = sorted(updates, key=lambda x: (x["driftScore"], -x["updated_weight"]), reverse=True)[:3]

    summary = {
        "schema": "attention_update_summary_v1",
        "created_at": created_at,
        "total_targets_updated": len(updates),
        "reinforced_targets": len(reinforced),
        "attenuated_targets": len(attenuated),
        "top_priority_concepts": [
            {
                "targetId": row["targetId"],
                "driftScore": row["driftScore"],
                "updated_weight": row["updated_weight"],
                "governing_rule": row["governing_rule"],
            }
            for row in top_priority
        ],
    }

    _validate_against_schema(payload, ATTENTION_SCHEMA_PATH)
    return payload, summary


def main() -> int:
    payload, summary = build_attention_updates()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    ATTENTION_UPDATES_OUT.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    ATTENTION_SUMMARY_OUT.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {ATTENTION_UPDATES_OUT}")
    print(f"Wrote {ATTENTION_SUMMARY_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
