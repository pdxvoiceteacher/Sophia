from sophia.governance.policy import DEFAULT_DIVERGENCE_POLICY
from sophia.governance.risk_classifier import classify_risk_from_packet


def _extract_track_signals(packet: dict) -> list[dict]:
    raw = packet.get("termination_signals", [])
    if isinstance(raw, dict):
        return [{"track_id": "unknown", "signals": raw}]
    if isinstance(raw, list):
        return raw
    return []


def _worst_track(track_signals: list[dict]) -> dict | None:
    if not track_signals:
        return None

    def severity(item: dict):
        s = item.get("signals", {})
        return (
            float(s.get("diverging", False)),
            float(s.get("oscillating", False)),
            float(s.get("stagnant", False)),
            float(s.get("lambda", 0.0)),
            float(s.get("deltaS", 0.0)),
            float(s.get("track_divergence", 0.0)),
            float(s.get("iteration", 0)),
        )

    return max(track_signals, key=severity)


def evaluate_divergence(packet: dict, policy: dict | None = None) -> dict:
    policy = policy or DEFAULT_DIVERGENCE_POLICY

    tier = classify_risk_from_packet(packet)
    cfg = policy["tiers"][tier]

    track_signals = _extract_track_signals(packet)
    worst = _worst_track(track_signals)

    if worst is None:
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "missing_termination_signals",
        }

    track_id = worst.get("track_id", "unknown")
    t = worst.get("signals", {})

    deltaS = float(t.get("deltaS", 0.0))
    lambda_val = float(t.get("lambda", 0.0))
    iteration = int(t.get("iteration", 0))

    if iteration >= cfg["max_iterations"]:
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "iteration_budget_exhausted",
            "track_id": track_id,
        }

    if lambda_val > cfg["max_lambda"] or deltaS > cfg["max_deltaS"]:
        if cfg["allow_exploration"]:
            return {
                "risk_tier": tier,
                "directive": "redirect",
                "reason": "divergence_exceeds_policy_but_exploration_allowed",
                "track_id": track_id,
                "deltaS": deltaS,
                "lambda": lambda_val,
            }
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "divergence_exceeds_policy",
            "track_id": track_id,
            "deltaS": deltaS,
            "lambda": lambda_val,
        }

    if bool(t.get("oscillating", False)):
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "oscillation_convergence",
            "track_id": track_id,
        }

    if bool(t.get("stagnant", False)):
        return {
            "risk_tier": tier,
            "directive": "redirect",
            "reason": "stagnation_detected",
            "track_id": track_id,
        }

    if bool(t.get("diverging", False)):
        if cfg["allow_exploration"]:
            return {
                "risk_tier": tier,
                "directive": "redirect",
                "reason": "divergence_detected_within_exploration_band",
                "track_id": track_id,
                "deltaS": deltaS,
                "lambda": lambda_val,
            }
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "divergence_detected",
            "track_id": track_id,
            "deltaS": deltaS,
            "lambda": lambda_val,
        }

    return {
        "risk_tier": tier,
        "directive": "continue",
        "reason": "within_policy_band",
        "track_id": track_id,
        "deltaS": deltaS,
        "lambda": lambda_val,
    }
