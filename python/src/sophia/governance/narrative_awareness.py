def interpret_narrative_overlay(packet: dict) -> dict:
    overlay = packet.get("narrative_overlay", {})
    activated = overlay.get("activated_modules", [])

    return {
        "narrative_flags": activated,
        "care_bias": "care_system_constructor" in activated,
        "anti_coercion_bias": "non_enslavement_constraint_kernel" in activated,
        "humanization_bias": "humanization_engine" in activated,
    }
