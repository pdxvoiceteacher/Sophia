def route_prior_injection(routing_packet: dict, atlas_prior_packet: dict) -> dict:
    """
    Decide whether Atlas priors should be injected into the active run.
    Modes:
      - answer_support
      - novelty_extension
      - background_only
      - ignore
    """
    relevance = routing_packet.get("answer_relevance_packet", {}).get("ranked_relevance", [])
    novelty = routing_packet.get("novelty_packet", {}).get("ranked_novelty", [])

    best_relevance = relevance[0] if relevance else None
    best_novelty = novelty[0] if novelty else None

    match_count = atlas_prior_packet.get("match_count", 0)
    top_similarity = 0.0
    if atlas_prior_packet.get("matches"):
        top_similarity = atlas_prior_packet["matches"][0].get("similarity_score", 0.0)

    mode = "ignore"
    reason = "No relevant priors available."
    confidence = 0.2

    if match_count == 0:
        return {
            "prior_injection_mode": mode,
            "prior_injection_reason": reason,
            "prior_injection_confidence": confidence,
        }

    if (
        best_relevance
        and best_relevance["relevance"]["relevance_score"] >= 6
        and top_similarity >= 0.15
    ):
        mode = "answer_support"
        reason = "Relevant Atlas priors can strengthen the direct answer path."
        confidence = 0.8
    elif (
        best_novelty
        and best_novelty["novelty"]["novelty_score"] >= 8
        and top_similarity >= 0.15
    ):
        mode = "novelty_extension"
        reason = "Relevant Atlas priors may broaden the novelty corridor."
        confidence = 0.7
    elif top_similarity >= 0.1:
        mode = "background_only"
        reason = (
            "Relevant Atlas priors are available but should not dominate the current answer."
        )
        confidence = 0.55

    return {
        "prior_injection_mode": mode,
        "prior_injection_reason": reason,
        "prior_injection_confidence": confidence,
    }
