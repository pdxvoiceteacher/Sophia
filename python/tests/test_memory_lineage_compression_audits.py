from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from sophia import audit_memory_lineage_compression_state as module


def _write(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _registry() -> dict:
    return {
        "schemaVersion": "phase_lineage_registry_v1",
        "phases": [
            {
                "phaseId": "BF",
                "phaseName": "civilizational-delta",
                "upstreamArtifacts": ["bridge/missing_upstream_example.json"],
                "downstreamArtifacts": ["bridge/civilizational_delta_audit.json"],
                "preservedConstraints": ["anti-canon-closure"],
                "transformedConcepts": ["delta detection"],
                "keyStatuses": ["delta-visible"],
                "humanMeaning": "m",
                "operatorQuestionsAnswered": ["q"],
                "relatedDocs": ["README.md"],
                "canonicalBoundaryNote": "b",
            },
            {
                "phaseId": "BO",
                "phaseName": "background-coherence",
                "upstreamArtifacts": ["bridge/living_terrace_audit.json"],
                "downstreamArtifacts": ["bridge/background_coherence_audit.json"],
                "preservedConstraints": ["non-priestly ordinariness"],
                "transformedConcepts": ["normalization"],
                "keyStatuses": ["background-visible", "keep-open"],
                "humanMeaning": "m2",
                "operatorQuestionsAnswered": ["q2"],
                "relatedDocs": ["README.md"],
                "canonicalBoundaryNote": "b2",
            },
        ],
    }


def _expected_hash(phase: dict) -> list[str]:
    import hashlib

    seed = f"{phase['phaseId']}|{','.join(phase['downstreamArtifacts'])}|{','.join(phase['keyStatuses'])}"
    d = hashlib.sha256(seed.encode()).hexdigest()
    return [f"sha256:{d[:16]}", f"sha256:{d[16:32]}"]


def _trace(valid: bool = True, invalid_tier: bool = False) -> dict:
    reg = _registry()["phases"]
    bf_hash = _expected_hash(reg[0])
    bo_hash = _expected_hash(reg[1])
    if not valid:
        bo_hash = ["sha256:bad", "sha256:hash"]
    return {
        "schemaVersion": "coherence_memory_trace_v1",
        "trace": [
            {"phaseId": "BF", "memoryTier": "cold", "artifactLineageHashes": bf_hash},
            {"phaseId": "BO", "memoryTier": "strange" if invalid_tier else "hot", "artifactLineageHashes": bo_hash},
        ],
    }


def test_outputs_and_issue_detection(monkeypatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(b / "phase_lineage_registry.json", _registry())
    _write(b / "coherence_memory_trace.json", _trace(valid=False, invalid_tier=True))
    _write(s / "memory_compression_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/memory_compression_audit_v1.schema.json").read_text()))
    _write(s / "lineage_integrity_report_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/lineage_integrity_report_v1.schema.json").read_text()))
    _write(s / "compression_recommendations_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/compression_recommendations_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "COHERENCE_MEMORY_TRACE_PATH", b / "coherence_memory_trace.json")
    monkeypatch.setattr(module, "PHASE_LINEAGE_REGISTRY_PATH", b / "phase_lineage_registry.json")
    monkeypatch.setattr(module, "MEMORY_COMPRESSION_AUDIT_SCHEMA_PATH", s / "memory_compression_audit_v1.schema.json")
    monkeypatch.setattr(module, "LINEAGE_INTEGRITY_REPORT_SCHEMA_PATH", s / "lineage_integrity_report_v1.schema.json")
    monkeypatch.setattr(module, "COMPRESSION_RECOMMENDATIONS_SCHEMA_PATH", s / "compression_recommendations_v1.schema.json")

    mem, lin, rec = module.build_outputs()

    assert mem["totalMemoryEntries"] == 2
    assert mem["warmMemoryUsage"] == 1  # invalid tier normalized
    assert len(mem["invariantHashChecks"]) == 1
    assert any("Keep-open" in r for r in mem["recommendations"])

    assert lin["lineageComplete"] is False
    assert "bridge/missing_upstream_example.json" in lin["missingLinks"]

    assert rec["actionItems"]

    Draft202012Validator(json.loads((s / "memory_compression_audit_v1.schema.json").read_text())).validate(mem)
    Draft202012Validator(json.loads((s / "lineage_integrity_report_v1.schema.json").read_text())).validate(lin)
    Draft202012Validator(json.loads((s / "compression_recommendations_v1.schema.json").read_text())).validate(rec)


def test_boundary_language_in_outputs(monkeypatch, tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    s = tmp_path / "schema"
    _write(b / "phase_lineage_registry.json", _registry())
    _write(b / "coherence_memory_trace.json", _trace(valid=True, invalid_tier=False))
    _write(s / "memory_compression_audit_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/memory_compression_audit_v1.schema.json").read_text()))
    _write(s / "lineage_integrity_report_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/lineage_integrity_report_v1.schema.json").read_text()))
    _write(s / "compression_recommendations_v1.schema.json", json.loads(Path("/workspace/Sophia/schema/compression_recommendations_v1.schema.json").read_text()))

    monkeypatch.setattr(module, "COHERENCE_MEMORY_TRACE_PATH", b / "coherence_memory_trace.json")
    monkeypatch.setattr(module, "PHASE_LINEAGE_REGISTRY_PATH", b / "phase_lineage_registry.json")
    monkeypatch.setattr(module, "MEMORY_COMPRESSION_AUDIT_SCHEMA_PATH", s / "memory_compression_audit_v1.schema.json")
    monkeypatch.setattr(module, "LINEAGE_INTEGRITY_REPORT_SCHEMA_PATH", s / "lineage_integrity_report_v1.schema.json")
    monkeypatch.setattr(module, "COMPRESSION_RECOMMENDATIONS_SCHEMA_PATH", s / "compression_recommendations_v1.schema.json")

    mem, lin, _ = module.build_outputs()
    text = " ".join(mem["recommendations"] + lin["recommendations"]).lower()
    assert "governance transfer" in text
    assert "canon closure" in text
    assert "automatic promotion" in text
    assert "automatic deletion" in text
    assert "epoch finalized" not in text
