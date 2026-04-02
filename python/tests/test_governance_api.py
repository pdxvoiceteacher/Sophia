from sophia.governance.divergence_governor import evaluate_divergence


def test_evaluate_divergence_minimal_packet():
    packet = {
        "risk_signals": {
            "lexical_flags": {
                "contains_safety_critical_terms": False,
                "contains_policy_terms": True,
                "contains_low_risk_terms": False,
            }
        },
        "termination_signals": {
            "deltaS": 0.0002,
            "lambda": 0.0003,
            "iteration": 3,
            "oscillating": False,
            "stagnant": False,
            "diverging": True,
        },
    }

    decision = evaluate_divergence(packet)
    assert "risk_tier" in decision
    assert "directive" in decision
    assert "reason" in decision
    assert "track_id" in decision
