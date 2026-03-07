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
REGIME_PATH = BRIDGE_DIR / "publication_regime_map.json"

COHERENCE_OUT = BRIDGE_DIR / "coherence_assessment.json"
RECOMMENDATIONS_OUT = BRIDGE_DIR / "sophia_recommendations.json"


@dataclass(slots=True)
class EvaluationResult:
    coherence_score: float
    risk_score: float
    regime_classification: str
    recommended_action: str
    explanation: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _count_items(payload: dict[str, Any], keys: tuple[str, ...]) -> int:
    for key in keys:
        v = payload.get(key)
        if isinstance(v, list):
            return len(v)
    return 0


def evaluate_graph_state(
    concept_map: dict[str, Any],
    constellation_map: dict[str, Any],
    publication_regime_map: dict[str, Any],
) -> EvaluationResult:
    concept_count = _count_items(concept_map, ("concepts", "nodes", "items"))
    constellation_count = _count_items(constellation_map, ("constellations", "edges", "relations"))

    instability = float(publication_regime_map.get("instability") or 0.0)
    conflict = float(publication_regime_map.get("conflict") or 0.0)
    safety = float(publication_regime_map.get("safety") or 1.0)

    coherence_raw = 0.55 + min(concept_count, 200) * 0.001 + min(constellation_count, 300) * 0.0007
    coherence_penalty = 0.25 * instability + 0.20 * conflict
    coherence_score = max(0.0, min(1.0, coherence_raw - coherence_penalty))

    risk_score = max(0.0, min(1.0, 0.55 * instability + 0.35 * conflict + 0.10 * (1.0 - safety)))

    if risk_score >= 0.80:
        regime = "critical"
        action = "prune"
        explanation = "High instability/conflict creates a critical publication regime; prune risky branches first."
    elif risk_score >= 0.60:
        regime = "elevated"
        action = "attenuate"
        explanation = "Risk is elevated relative to coherence; attenuate propagation and reduce amplification pressure."
    elif coherence_score >= 0.75 and risk_score <= 0.30:
        regime = "stable"
        action = "reinforce"
        explanation = "Coherence remains high with low risk; reinforce the strongest convergent lattice paths."
    else:
        regime = "watch"
        action = "observe"
        explanation = "State is mixed or borderline; continue observation before structural intervention."

    return EvaluationResult(
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        regime_classification=regime,
        recommended_action=action,
        explanation=explanation,
    )


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    concept_map = _load_json(CONCEPT_PATH)
    constellation_map = _load_json(CONSTELLATION_PATH)
    publication_regime_map = _load_json(REGIME_PATH)

    result = evaluate_graph_state(concept_map, constellation_map, publication_regime_map)
    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    assessment = {
        "schema": "coherence_assessment_v1",
        "created_at": now,
        "inputs": {
            "concept_lattice_map": str(CONCEPT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "constellation_lattice_map": str(CONSTELLATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "publication_regime_map": str(REGIME_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "coherenceScore": result.coherence_score,
        "riskScore": result.risk_score,
        "regimeClassification": result.regime_classification,
        "recommendedAction": result.recommended_action,
        "explanation": result.explanation,
    }

    recommendations = {
        "schema": "sophia_recommendations_v1",
        "created_at": now,
        "recommendations": [
            {
                "action": result.recommended_action,
                "priority": "high" if result.risk_score >= 0.6 else "normal",
                "explanation": result.explanation,
                "regimeClassification": result.regime_classification,
            }
        ],
        "actionCatalog": [
            {
                "action": "reinforce",
                "explanation": "Strengthen high-confidence links when coherence is high and risk is low.",
            },
            {
                "action": "observe",
                "explanation": "Monitor the graph state to gather more evidence before intervention.",
            },
            {
                "action": "attenuate",
                "explanation": "Reduce propagation intensity in unstable or conflict-heavy regions.",
            },
            {
                "action": "prune",
                "explanation": "Remove or quarantine high-risk branches when critical risk is detected.",
            },
        ],
    }

    return assessment, recommendations


def main() -> int:
    assessment, recommendations = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    COHERENCE_OUT.write_text(json.dumps(assessment, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {COHERENCE_OUT}")
    print(f"Wrote {RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
