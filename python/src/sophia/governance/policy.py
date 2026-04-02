DEFAULT_DIVERGENCE_POLICY = {
    "tiers": {
        "TRIVIAL": {
            "max_lambda": 0.001,
            "max_deltaS": 0.001,
            "allow_exploration": False,
            "max_iterations": 2,
            "response": "continue_or_stop_fast",
        },
        "ANALYTICAL": {
            "max_lambda": 0.00025,
            "max_deltaS": 0.00015,
            "allow_exploration": True,
            "max_iterations": 8,
            "response": "continue_redirect_or_halt",
        },
        "CRITICAL": {
            "max_lambda": 0.00015,
            "max_deltaS": 0.00010,
            "allow_exploration": False,
            "max_iterations": 12,
            "response": "redirect_or_halt",
        },
        "EXISTENTIAL": {
            "max_lambda": 0.00010,
            "max_deltaS": 0.00008,
            "allow_exploration": False,
            "max_iterations": 15,
            "response": "escalate_or_halt",
        },
    }
}
