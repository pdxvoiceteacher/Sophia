def route_relevance_and_novelty(routing_packet: dict) -> dict:
    rel = routing_packet.get("answer_relevance_packet", {}).get("ranked_relevance", [])
    nov = routing_packet.get("novelty_packet", {}).get("ranked_novelty", [])

    best_relevance = rel[0] if rel else None
    best_novelty = nov[0] if nov else None

    novelty_action = "hold"
    atlas_route_confidence = 0.2
    atlas_route_reason = "Novelty below routing threshold."

    if best_novelty:
        nscore = best_novelty["novelty"]["novelty_score"]
        if nscore >= 8:
            novelty_action = "send_to_atlas"
            atlas_route_confidence = 0.85
            atlas_route_reason = (
                "Novelty score is high enough to send to Atlas for adjudication."
            )
        elif nscore >= 4:
            novelty_action = "hold_for_review"
            atlas_route_confidence = 0.55
            atlas_route_reason = (
                "Novelty is moderate; preserve for possible Atlas routing later."
            )

    decision = {
        "return_track_id": best_relevance["track_id"] if best_relevance else None,
        "return_reason": "highest_governed_relevance" if best_relevance else "none",
        "novel_track_id": best_novelty["track_id"] if best_novelty else None,
        "novelty_action": novelty_action,
        "atlas_route_confidence": atlas_route_confidence,
        "atlas_route_reason": atlas_route_reason,
        "clarification_needed": False,
        "clarification_reason": None,
    }

    if best_relevance and best_relevance["relevance"]["relevance_score"] <= 2:
        decision["clarification_needed"] = True
        decision["clarification_reason"] = (
            "Low direct answer relevance; user/context clarification may improve routing."
        )

    return decision
