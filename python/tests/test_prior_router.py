import json
from pathlib import Path

from sophia.api.server import govern_prior_injection
from sophia.governance.prior_router import route_prior_injection


def test_route_prior_injection_ignore_when_no_matches() -> None:
    decision = route_prior_injection({}, {"match_count": 0})

    assert decision == {
        "prior_injection_mode": "ignore",
        "prior_injection_reason": "No relevant priors available.",
        "prior_injection_confidence": 0.2,
    }


def test_route_prior_injection_answer_support() -> None:
    routing_packet = {
        "answer_relevance_packet": {
            "ranked_relevance": [{"relevance": {"relevance_score": 7}}]
        }
    }
    atlas_prior_packet = {"match_count": 1, "matches": [{"similarity_score": 0.2}]}

    decision = route_prior_injection(routing_packet, atlas_prior_packet)

    assert decision["prior_injection_mode"] == "answer_support"
    assert decision["prior_injection_confidence"] == 0.8


def test_route_prior_injection_novelty_extension() -> None:
    routing_packet = {
        "novelty_packet": {"ranked_novelty": [{"novelty": {"novelty_score": 9}}]}
    }
    atlas_prior_packet = {"match_count": 1, "matches": [{"similarity_score": 0.2}]}

    decision = route_prior_injection(routing_packet, atlas_prior_packet)

    assert decision["prior_injection_mode"] == "novelty_extension"


def test_govern_prior_injection_reads_inputs_and_writes_output(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)

    routing_packet = {
        "answer_relevance_packet": {
            "ranked_relevance": [{"relevance": {"relevance_score": 7}}]
        }
    }
    prior_packet = {"match_count": 1, "matches": [{"similarity_score": 0.2}]}

    routing_path = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_packet.json")
    prior_path = Path(r"C:\UVLM\CoherenceLattice\bridge\atlas_prior_packet.json")
    routing_path.write_text(json.dumps(routing_packet), encoding="utf-8")
    prior_path.write_text(json.dumps(prior_packet), encoding="utf-8")

    decision = govern_prior_injection()

    assert decision["prior_injection_mode"] == "answer_support"
    out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\prior_injection_decision.json")
    saved = json.loads(out_path.read_text(encoding="utf-8"))
    assert saved == decision
