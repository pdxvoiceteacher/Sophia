import json
from pathlib import Path

from sophia.api.server import govern_routing
from sophia.governance.relevance_router import route_relevance_and_novelty


def test_route_relevance_and_novelty_defaults() -> None:
    result = route_relevance_and_novelty({})

    assert result == {
        "return_track_id": None,
        "return_reason": "none",
        "novel_track_id": None,
        "novelty_action": "hold",
        "atlas_route_confidence": 0.2,
        "atlas_route_reason": "Novelty below routing threshold.",
        "clarification_needed": False,
        "clarification_reason": None,
    }


def test_route_relevance_and_novelty_with_high_novelty() -> None:
    packet = {
        "answer_relevance_packet": {
            "ranked_relevance": [
                {"track_id": "t1", "relevance": {"relevance_score": 2}},
            ]
        },
        "novelty_packet": {
            "ranked_novelty": [
                {"track_id": "n1", "novelty": {"novelty_score": 9}},
            ]
        },
    }

    result = route_relevance_and_novelty(packet)

    assert result["return_track_id"] == "t1"
    assert result["novel_track_id"] == "n1"
    assert result["novelty_action"] == "send_to_atlas"
    assert result["atlas_route_confidence"] == 0.85
    assert "Atlas" in result["atlas_route_reason"]
    assert result["clarification_needed"] is True


def test_route_relevance_and_novelty_with_moderate_novelty() -> None:
    packet = {
        "answer_relevance_packet": {
            "ranked_relevance": [
                {"track_id": "t3", "relevance": {"relevance_score": 7}},
            ]
        },
        "novelty_packet": {
            "ranked_novelty": [
                {"track_id": "n3", "novelty": {"novelty_score": 4}},
            ]
        },
    }

    result = route_relevance_and_novelty(packet)

    assert result["novelty_action"] == "hold_for_review"
    assert result["atlas_route_confidence"] == 0.55
    assert "moderate" in result["atlas_route_reason"]


def test_govern_routing_reads_packet_and_writes_decision(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)
    packet = {
        "answer_relevance_packet": {
            "ranked_relevance": [
                {"track_id": "t2", "relevance": {"relevance_score": 6}},
            ]
        },
        "novelty_packet": {
            "ranked_novelty": [
                {"track_id": "n2", "novelty": {"novelty_score": 9}},
            ]
        },
    }
    packet_file = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_packet.json")
    packet_file.write_text(json.dumps(packet), encoding="utf-8")

    result = govern_routing()

    assert result["return_track_id"] == "t2"
    assert result["novelty_action"] == "send_to_atlas"
    assert "atlas_route_confidence" in result
    assert "atlas_route_reason" in result
    decision_file = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_decision.json")
    saved = json.loads(decision_file.read_text(encoding="utf-8"))
    assert saved == result
