def classify_risk_from_packet(packet: dict) -> str:
    signals = packet.get("risk_signals", {})
    lexical = signals.get("lexical_flags", {})

    if lexical.get("contains_safety_critical_terms"):
        return "CRITICAL"

    if lexical.get("contains_low_risk_terms"):
        return "TRIVIAL"

    if lexical.get("contains_policy_terms"):
        return "ANALYTICAL"

    return "ANALYTICAL"
