import json
from pathlib import Path

from sophia.api.server import govern_divergence
from sophia.governance.divergence_governor import evaluate_divergence
from sophia.governance.policy import DEFAULT_DIVERGENCE_POLICY
from sophia.governance.risk_classifier import classify_risk_from_packet
from sophia.governance.store import save_governance_decision


def test_classify_risk_from_packet() -> None:
    assert (
        classify_risk_from_packet(
            {"risk_signals": {"lexical_flags": {"contains_safety_critical_terms": True}}}
        )
        == "CRITICAL"
    )
    assert (
        classify_risk_from_packet(
            {"risk_signals": {"lexical_flags": {"contains_low_risk_terms": True}}}
        )
        == "TRIVIAL"
    )
    assert (
        classify_risk_from_packet(
            {"risk_signals": {"lexical_flags": {"contains_policy_terms": True}}}
        )
        == "ANALYTICAL"
    )


def test_evaluate_divergence_halts_on_iteration_budget() -> None:
    packet = {
        "risk_signals": {"lexical_flags": {"contains_low_risk_terms": True}},
        "termination_signals": {"iteration": 2},
    }

    result = evaluate_divergence(packet)

    assert result == {
        "risk_tier": "TRIVIAL",
        "directive": "halt",
        "reason": "iteration_budget_exhausted",
    }


def test_evaluate_divergence_redirects_when_exploration_allowed() -> None:
    packet = {
        "risk_signals": {"lexical_flags": {"contains_policy_terms": True}},
        "termination_signals": {"lambda": 0.001},
    }

    result = evaluate_divergence(packet)

    assert result == {
        "risk_tier": "ANALYTICAL",
        "directive": "redirect",
        "reason": "divergence_exceeds_policy_but_exploration_allowed",
    }


def test_evaluate_divergence_continues_within_policy_band() -> None:
    packet = {
        "risk_signals": {"lexical_flags": {"contains_policy_terms": True}},
        "termination_signals": {
            "deltaS": 0.0,
            "lambda": 0.0,
            "iteration": 0,
        },
    }

    result = evaluate_divergence(packet, policy=DEFAULT_DIVERGENCE_POLICY)

    assert result == {
        "risk_tier": "ANALYTICAL",
        "directive": "continue",
        "reason": "within_policy_band",
    }


def test_save_governance_decision(tmp_path: Path) -> None:
    decision = {"directive": "continue", "risk_tier": "ANALYTICAL"}
    out = tmp_path / "bridge" / "governance_decision.json"

    save_governance_decision(decision, out)

    assert out.exists()
    assert json.loads(out.read_text(encoding="utf-8")) == decision


def test_govern_divergence_returns_error_without_packet(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.chdir(tmp_path)

    result = govern_divergence()

    assert "governance_packet.json not found at" in result["error"]


def test_govern_divergence_reads_packet_and_writes_decision(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)
    bridge = tmp_path / "bridge"
    bridge.mkdir(parents=True)
    packet = {
        "risk_signals": {"lexical_flags": {"contains_policy_terms": True}},
        "termination_signals": {"deltaS": 0.0, "lambda": 0.0, "iteration": 0},
    }
    (bridge / "governance_packet.json").write_text(
        json.dumps(packet), encoding="utf-8"
    )

    result = govern_divergence()

    assert result["directive"] == "continue"
    saved = json.loads((bridge / "governance_decision.json").read_text(encoding="utf-8"))
    assert saved == result
