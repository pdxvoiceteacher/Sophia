from sophia.governance.policy import DEFAULT_DIVERGENCE_POLICY
from sophia.governance.risk_classifier import classify_risk_from_packet


def evaluate_divergence(packet: dict, policy: dict | None = None) -> dict:
    policy = policy or DEFAULT_DIVERGENCE_POLICY

    tier = classify_risk_from_packet(packet)
    cfg = policy["tiers"][tier]

    t = packet.get("termination_signals", {})

    deltaS = t.get("deltaS", 0.0)
    lambda_val = t.get("lambda", 0.0)
    iteration = t.get("iteration", 0)

    if iteration >= cfg["max_iterations"]:
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "iteration_budget_exhausted",
        }

    if lambda_val > cfg["max_lambda"] or deltaS > cfg["max_deltaS"]:
        if cfg["allow_exploration"]:
            return {
                "risk_tier": tier,
                "directive": "redirect",
                "reason": "divergence_exceeds_policy_but_exploration_allowed",
            }
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "divergence_exceeds_policy",
        }

    if t.get("oscillating"):
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "oscillation_convergence",
        }

    if t.get("stagnant"):
        return {
            "risk_tier": tier,
            "directive": "redirect",
            "reason": "stagnation_detected",
        }

    if t.get("diverging"):
        if cfg["allow_exploration"]:
            return {
                "risk_tier": tier,
                "directive": "redirect",
                "reason": "divergence_detected_within_exploration_band",
            }
        return {
            "risk_tier": tier,
            "directive": "halt",
            "reason": "divergence_detected",
        }

    return {
        "risk_tier": tier,
        "directive": "continue",
        "reason": "within_policy_band",
    }
