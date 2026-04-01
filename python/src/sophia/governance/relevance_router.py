def route_relevance_and_novelty(routing_packet: dict) -> dict:
    rel = routing_packet.get("answer_relevance_packet", {}).get("ranked_relevance", [])
    nov = routing_packet.get("novelty_packet", {}).get("ranked_novelty", [])

    best_relevance = rel[0] if rel else None
    best_novelty = nov[0] if nov else None

    decision = {
        "return_track_id": best_relevance["track_id"] if best_relevance else None,
        "return_reason": "highest_governed_relevance" if best_relevance else "none",
        "novel_track_id": best_novelty["track_id"] if best_novelty else None,
        "novelty_action": "log_to_atlas"
        if best_novelty and best_novelty["novelty"]["novelty_score"] >= 8
        else "ignore_or_hold",
        "clarification_needed": False,
        "clarification_reason": None,
    }

    # If top novelty is high but relevance is weak, keep user answer on task but preserve novelty
    if best_relevance and best_relevance["relevance"]["relevance_score"] <= 2:
        decision["clarification_needed"] = True
        decision["clarification_reason"] = (
            "Low direct answer relevance; user/context clarification may improve routing."
        )

    return decision
