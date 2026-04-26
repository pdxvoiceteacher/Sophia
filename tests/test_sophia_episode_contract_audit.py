from __future__ import annotations

import json
from pathlib import Path

from tools.telemetry.sophia_audit import read_episode_contract_audit


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_episode_contract_audit_reports_fields_and_warnings_without_mutation(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"

    _write(bridge / "governance_decision.json", {"directive": "defer"})
    _write(bridge / "routing_decision.json", {"return_track_id": "track.alpha"})
    _write(bridge / "selection_authority_packet.json", {"final_answer_source_track_id": "track.alpha"})
    _write(bridge / "prior_injection_decision.json", {"prior_injection_mode": "quote"})
    _write(bridge / "atlas_prior_packet.json", {"selected_priors": [{"prior_id": "p1", "allowed_use": "cite_only"}]})
    _write(bridge / "triadic_run_manifest.json", {"run_id": "run-123"})
    _write(bridge / "source_evidence_packet.json", {})
    _write(bridge / "final_answer.json", {"source": "track.beta"})

    before = {p.name for p in bridge.iterdir()}
    report = read_episode_contract_audit(bridge)
    after = {p.name for p in bridge.iterdir()}

    assert report["governance_decision"]["directive"] == "defer"
    assert report["routing_decision"]["return_track_id"] == "track.alpha"
    assert report["selection_authority_packet"]["final_answer_source_track_id"] == "track.alpha"
    assert report["prior_injection_decision"]["prior_injection_mode"] == "quote"
    assert report["atlas_prior_packet"]["selected_priors"][0]["allowed_use"] == "cite_only"
    assert report["triadic_run_manifest"]["run_id"] == "run-123"
    assert report["source_evidence_packet"]["source_id"] is None
    assert report["final_answer"]["source"] == "track.beta"

    warning_codes = {w["code"] for w in report["warnings"]}
    assert "final_answer_source_mismatch" in warning_codes
    assert "prior_injection_mode_exceeds_allowed_use" in warning_codes
    assert "missing_preset" in warning_codes
    assert "missing_source_id" in warning_codes

    assert before == after
