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
        "novelty_action": "ignore_or_hold",
        "clarification_needed": False,
        "clarification_reason": None,
    }


def test_route_relevance_and_novelty_with_scores() -> None:
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
    assert result["novelty_action"] == "log_to_atlas"
    assert result["clarification_needed"] is True


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
                {"track_id": "n2", "novelty": {"novelty_score": 4}},
            ]
        },
    }
    packet_file = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_packet.json")
    packet_file.write_text(json.dumps(packet), encoding="utf-8")

    result = govern_routing()

    assert result["return_track_id"] == "t2"
    decision_file = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_decision.json")
    saved = json.loads(decision_file.read_text(encoding="utf-8"))
    assert saved == result
