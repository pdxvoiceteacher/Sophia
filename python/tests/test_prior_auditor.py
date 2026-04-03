import json
from pathlib import Path

from sophia.api.server import govern_prior_audit
from sophia.governance.prior_auditor import audit_prior_use


def test_audit_prior_use_pass_case() -> None:
    packet = {
        "question_text": "What is the energy policy outlook?",
        "final_answer": "The energy policy outlook remains policy-focused and stable.",
        "prior_injection_mode": "answer_support",
        "source_terms": ["policy", "energy"],
        "prior_injection_trace": {
            "selected_priors": [{"excerpt": "Energy policy outlook remains stable."}]
        },
        "expected_return_track_id": "t1",
        "answer_source_track": "t1",
    }

    decision = audit_prior_use(packet)

    assert decision["formal_auditor"] == "Sophia"
    assert decision["audit_status"] == "pass"
    assert decision["recommendation"] == "keep"


def test_audit_prior_use_warn_for_ignore_mode_with_influence() -> None:
    packet = {
        "question_text": "What are safe defaults?",
        "final_answer": "Historical kernel extraction and feature ridge pathways are dominant.",
        "prior_injection_mode": "ignore",
        "prior_injection_trace": {
            "selected_priors": [
                {
                    "excerpt": "Historical kernel extraction and feature ridge pathways are dominant.",
                }
            ]
        },
    }

    decision = audit_prior_use(packet)

    assert decision["audit_status"] == "warn"
    assert decision["mode_compliance"] is False


def test_audit_prior_use_warn_for_routing_mismatch() -> None:
    packet = {
        "question_text": "What is governance routing?",
        "final_answer": "Governance routing returns track A.",
        "prior_injection_mode": "background_only",
        "expected_return_track_id": "A",
        "answer_source_track": "B",
    }

    decision = audit_prior_use(packet)

    assert decision["audit_status"] == "warn"
    assert "does not match" in decision["audit_reason"]


def test_audit_prior_use_detects_prompt_contamination() -> None:
    packet = {
        "question_text": "[ATLAS PRIOR INJECTION START] contaminated",
        "final_answer": "anything",
    }

    decision = audit_prior_use(packet)

    assert decision["audit_status"] == "warn"
    assert decision["recommendation"] == "fix_question_integrity_before_trusting_prior_use_audit"


def test_govern_prior_audit_reads_packet_and_writes_decision(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)
    packet = {
        "question_text": "How should novelty be routed?",
        "final_answer": "Novelty should be routed to Atlas with review safeguards.",
        "prior_injection_mode": "novelty_extension",
        "prior_injection_trace": {
            "selected_priors": [
                {"excerpt": "Novelty routed to Atlas with safeguards and review."}
            ]
        },
    }

    packet_path = Path(r"C:\UVLM\CoherenceLattice\bridge\prior_use_audit_packet.json")
    packet_path.write_text(json.dumps(packet), encoding="utf-8")

    decision = govern_prior_audit()

    assert "audit_status" in decision
    out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\prior_audit_decision.json")
    saved = json.loads(out_path.read_text(encoding="utf-8"))
    assert saved == decision
