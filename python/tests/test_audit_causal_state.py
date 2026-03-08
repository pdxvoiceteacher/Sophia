from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_causal_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "causal_bundle_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.causal.fixture",
        "producerCommit": "fixture-u-0001",
        "generatedAt": "2026-04-03T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-03T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "CAUSAL_BUNDLE_MAP_PATH", tmp_path / "bridge/causal_bundle_map.json")
    monkeypatch.setattr(module, "MECHANISM_CANDIDATE_MAP_PATH", tmp_path / "bridge/mechanism_candidate_map.json")
    monkeypatch.setattr(module, "MECHANISM_SEPARATION_REPORT_PATH", tmp_path / "bridge/mechanism_separation_report.json")
    monkeypatch.setattr(module, "CAUSAL_CONFLICT_REPORT_PATH", tmp_path / "bridge/causal_conflict_report.json")
    monkeypatch.setattr(module, "PATTERN_TEMPORAL_AUDIT_PATH", tmp_path / "bridge/pattern_temporal_audit.json")
    monkeypatch.setattr(module, "ENVIRONMENT_AUDIT_PATH", tmp_path / "bridge/environment_audit.json")
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_AUDIT_PATH", tmp_path / "bridge/evidence_authority_audit.json")
    monkeypatch.setattr(module, "VERIFICATION_AUDIT_PATH", tmp_path / "bridge/verification_audit.json")
    monkeypatch.setattr(module, "CAUSAL_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/causal_audit_v1.schema.json"))
    monkeypatch.setattr(module, "CAUSAL_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/causal_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "causal_bundle_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "bundle", "persistenceScore": 0.7, "bundleCoherence": 0.65},
                    {"targetId": "target:a", "targetType": "bundle", "persistenceScore": 0.6, "bundleCoherence": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "mechanism_candidate_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "mechanismConfidence": 0.64, "explanatoryMaturity": 0.60},
                    {"targetId": "target:a", "mechanismConfidence": 0.56, "explanatoryMaturity": 0.54},
                ]
            }
        ),
    )
    _write_json(
        bridge / "mechanism_separation_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "mechanismOverlap": 0.35, "separationQuality": 0.68},
                    {"targetId": "target:a", "mechanismOverlap": 0.42, "separationQuality": 0.62},
                ]
            }
        ),
    )
    _write_json(
        bridge / "causal_conflict_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "conflictScore": 0.34, "counterHypothesisStrength": 0.44},
                    {"targetId": "target:a", "conflictScore": 0.40, "counterHypothesisStrength": 0.48},
                ]
            }
        ),
    )

    for name in (
        "pattern_temporal_audit.json",
        "environment_audit.json",
        "evidence_authority_audit.json",
        "verification_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/causal_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/causal_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_causal_status_coverage() -> None:
    cases = [
        (
            "provisional",
            {"persistenceScore": 0.78, "bundleCoherence": 0.72},
            {"mechanismConfidence": 0.70, "explanatoryMaturity": 0.68},
            {"mechanismOverlap": 0.24, "separationQuality": 0.76},
            {"conflictScore": 0.28, "counterHypothesisStrength": 0.40},
            "mechanism-provisional",
        ),
        (
            "watch",
            {"persistenceScore": 0.62, "bundleCoherence": 0.58},
            {"mechanismConfidence": 0.62, "explanatoryMaturity": 0.58},
            {"mechanismOverlap": 0.70, "separationQuality": 0.42},
            {"conflictScore": 0.52, "counterHypothesisStrength": 0.46},
            "mechanism-watch",
        ),
        (
            "verify",
            {"persistenceScore": 0.60, "bundleCoherence": 0.56},
            {"mechanismConfidence": 0.70, "explanatoryMaturity": 0.34},
            {"mechanismOverlap": 0.45, "separationQuality": 0.56},
            {"conflictScore": 0.44, "counterHypothesisStrength": 0.48},
            "mechanism-verify-first",
        ),
        (
            "human",
            {"persistenceScore": 0.58, "bundleCoherence": 0.50},
            {"mechanismConfidence": 0.60, "explanatoryMaturity": 0.56},
            {"mechanismOverlap": 0.50, "separationQuality": 0.54},
            {"conflictScore": 0.86, "counterHypothesisStrength": 0.80},
            "mechanism-require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, candidate, separation, conflict, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "bundle", **row},
            candidate_rows={target_id: candidate},
            separation_rows={target_id: separation},
            conflict_rows={target_id: conflict},
            system_risk=0.35,
        )
        statuses.add(decision.causal_status)
        assert decision.causal_status == expected

    assert statuses == {
        "mechanism-watch",
        "mechanism-verify-first",
        "mechanism-provisional",
        "mechanism-require-human-review",
    }


def test_non_accusatory_bounded_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "bundle", "persistenceScore": 0.60, "bundleCoherence": 0.58},
        candidate_rows={"tone": {"mechanismConfidence": 0.62, "explanatoryMaturity": 0.55}},
        separation_rows={"tone": {"mechanismOverlap": 0.40, "separationQuality": 0.62}},
        conflict_rows={"tone": {"conflictScore": 0.42, "counterHypothesisStrength": 0.54}},
        system_risk=0.34,
    )

    text = " ".join(
        [
            decision.persistence_context,
            decision.mechanism_context,
            decision.counter_hypothesis_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "guilty" not in text
    assert "conspiracy" not in text
    assert "corruption" not in text


def test_explanatory_gap_handling() -> None:
    decision = module.evaluate_target(
        {"targetId": "gap", "targetType": "bundle", "persistenceScore": 0.62, "bundleCoherence": 0.58},
        candidate_rows={"gap": {"mechanismConfidence": 0.78, "explanatoryMaturity": 0.48}},
        separation_rows={"gap": {"mechanismOverlap": 0.42, "separationQuality": 0.60}},
        conflict_rows={"gap": {"conflictScore": 0.44, "counterHypothesisStrength": 0.42}},
        system_risk=0.35,
    )
    assert decision.causal_status == "mechanism-verify-first"
    assert decision.target_publisher_action == "suppress"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_bundle = _artifact(
        {
            "producerCommit": "",
            "targets": [{"targetId": "target:a", "targetType": "bundle", "persistenceScore": 0.60, "bundleCoherence": 0.58}],
        }
    )
    _write_json(tmp_path / "bridge/causal_bundle_map.json", bad_bundle)

    with pytest.raises(module.CausalInputError):
        module.build_outputs()
