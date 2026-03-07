from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from python.src.coherence.bridge import build_environment_integrity_state as mod


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _base() -> dict[str, str]:
    return {
        "schemaVersion": "x",
        "producerRepo": "Sophia",
        "producerModule": "tests",
        "producerCommit": "t",
        "generatedAt": "2026-04-01T00:00:00Z",
    }


def _setup(tmp_path: Path, monkeypatch) -> None:
    bridge = tmp_path / "bridge"
    reg = tmp_path / "registry"
    schema = Path(__file__).resolve().parents[1] / "schema"
    monkeypatch.setattr(mod, "BRIDGE_DIR", bridge)
    monkeypatch.setattr(mod, "REGISTRY_DIR", reg)
    monkeypatch.setattr(mod, "INPUTS", {
        "verification": bridge / "verification_task_map.json",
        "claim": bridge / "claim_type_map.json",
        "entity": bridge / "entity_resolution_map.json",
        "public_record": bridge / "public_record_intake_map.json",
        "custody": bridge / "chain_of_custody_report.json",
        "symbolic": bridge / "symbolic_field_state.json",
        "warning": bridge / "early_warning_signal_map.json",
        "verification_dashboard": reg / "verification_dashboard.json",
    })
    monkeypatch.setattr(mod, "OUTPUTS", {
        "environment": bridge / "environment_integrity_map.json",
        "anomaly": bridge / "anomaly_domain_map.json",
        "maturity": bridge / "evidence_maturity_report.json",
        "counter": bridge / "counter_hypothesis_map.json",
    })
    monkeypatch.setattr(mod, "SCHEMAS", {
        "environment": schema / "environment_integrity_map_v1.schema.json",
        "anomaly": schema / "anomaly_domain_map_v1.schema.json",
        "maturity": schema / "evidence_maturity_report_v1.schema.json",
        "counter": schema / "counter_hypothesis_map_v1.schema.json",
    })

    b = _base()
    _write(bridge / "verification_task_map.json", {**b, "targets": [{"targetId": "target:b", "targetType": "identity", "contradictionScore": 0.7}, {"targetId": "target:a", "targetType": "record", "contradictionScore": 0.2}]})
    _write(bridge / "claim_type_map.json", {**b, "targets": [{"targetId": "target:a", "claimType": "platform artifact"}, {"targetId": "target:b", "claimType": "coordinated behavior"}]})
    _write(bridge / "entity_resolution_map.json", {**b, "targets": [{"targetId": "target:a", "entityAmbiguity": 0.2}, {"targetId": "target:b", "entityAmbiguity": 0.7}]})
    _write(bridge / "public_record_intake_map.json", {**b, "targets": [{"targetId": "target:a", "recordQuality": 0.8, "claimReliability": 0.7}, {"targetId": "target:b", "recordQuality": 0.4, "claimReliability": 0.5}]})
    _write(bridge / "chain_of_custody_report.json", {**b, "targets": [{"targetId": "target:a", "chainCompleteness": 0.8, "tamperRisk": 0.2}, {"targetId": "target:b", "chainCompleteness": 0.3, "tamperRisk": 0.8}]})
    _write(bridge / "symbolic_field_state.json", {**b, "targets": [{"targetId": "target:a", "ambiguityScore": 0.2}, {"targetId": "target:b", "ambiguityScore": 0.7}]})
    _write(bridge / "early_warning_signal_map.json", {**b, "targets": [{"targetId": "target:a", "anomalyDomain": "digital", "attackSurfaceClass": "platform", "signalScore": 0.2}, {"targetId": "target:b", "anomalyDomain": "social_behavioral", "attackSurfaceClass": "social", "signalScore": 0.7}]})
    _write(reg / "verification_dashboard.json", {**b, "schemaVersion": "verification_dashboard_v1"})


def test_environment_integrity_outputs_and_ordering(tmp_path: Path, monkeypatch) -> None:
    _setup(tmp_path, monkeypatch)
    outputs = mod.build_outputs()
    mod.validate_outputs(outputs)
    mod.write_outputs(outputs)

    env_targets = outputs["environment"]["targets"]
    assert [t["targetId"] for t in env_targets] == ["target:a", "target:b"]
    assert {t["anomalyDomain"] for t in env_targets} == {"digital", "social_behavioral"}
    assert {t["attackSurfaceClass"] for t in env_targets} == {"platform", "social"}


def test_evidence_maturity_and_counter_hypothesis_behavior(tmp_path: Path, monkeypatch) -> None:
    _setup(tmp_path, monkeypatch)
    outputs = mod.build_outputs()
    maturity = {r["targetId"]: r for r in outputs["maturity"]["targets"]}
    assert maturity["target:a"]["maturityClass"] in {"independently_verified", "conclusion_ready"}
    assert maturity["target:b"]["maturityClass"] in {"artifact", "repeatable_test"}

    counter = {r["targetId"]: r for r in outputs["counter"]["targets"]}
    assert counter["target:b"]["recommendedClass"] in {"verify", "hold"}
    assert len(counter["target:a"]["counterHypotheses"]) >= 2


def test_schemas_validate_from_disk() -> None:
    repo = Path(__file__).resolve().parents[1]
    for schema_name in (
        "environment_integrity_map_v1.schema.json",
        "anomaly_domain_map_v1.schema.json",
        "evidence_maturity_report_v1.schema.json",
        "counter_hypothesis_map_v1.schema.json",
    ):
        payload = json.loads((repo / "schema" / schema_name).read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(payload)
