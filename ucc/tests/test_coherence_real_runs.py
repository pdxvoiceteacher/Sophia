from __future__ import annotations

import json
from pathlib import Path

from ucc.core import run_module


def _write_json(p: Path, obj: dict) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")


def _artifact_for_outputs(*, question: str, answer: str, sources: list[dict], claims: list[dict]) -> dict:
    # Minimal governance fields so E_s proxy passes
    return {
        "coherence_artifact": {
            "id": "ci-artifact",
            "domain": "research",
            "question": question,
            "answer": answer,
            "sections": {
                "assumptions": "Toy/coherence proxy; not a truth guarantee.",
                "limitations": "CI scaffold; checks structure and traceability proxies only.",
                "uncertainty": "Outputs depend on referenced artifacts and thresholds.",
                "disclosure": "Research scaffold only. Report issues via GitHub."
            },
            "claims": claims,
            "sources": sources,
            "evidence": {"links": ["https://github.com/pdxvoiceteacher/CoherenceLattice"], "artifacts": []},
            "review_cycle": {
                "cadence": "quarterly",
                "owner": "maintainers",
                "last_review_utc": "2026-01-01T00:00:00Z",
                "next_review_utc": "2026-04-01T00:00:00Z"
            },
            "exceptions": {
                "process": "CI scaffold exception for proxy metrics.",
                "items": [
                    {
                        "id": "EX-1",
                        "description": "Proxy-only audit in CI.",
                        "risk_acceptor": "maintainers",
                        "issued_utc": "2026-01-01T00:00:00Z",
                        "expires_utc": "2026-12-31T00:00:00Z"
                    }
                ]
            },
            "reporting_channel": {"primary": "github issues", "escalation": "maintainers"},
            "perturbations": [
                {"variant_id": "p1", "answer": answer, "decision_label": "accept"},
                {"variant_id": "p2", "answer": answer, "decision_label": "accept"}
            ]
        }
    }


def _assert_coherence_outputs(outdir: Path) -> None:
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()
    assert (outdir / "coherence_audit.json").exists()
    assert (outdir / "coherence_audit.md").exists()
    assert (outdir / "coherence_claims.csv").exists()


def test_coherence_run_helmholtz(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"

    # 1) Run Helmholtz comparator to tmp
    helm_mod = repo / "modules" / "helmholtz_compare.yml"
    helm_task = repo / "tasks" / "helmholtz_compare_sample.json"
    helm_out = tmp_path / "helmholtz_out"
    run_module(helm_mod, helm_task, helm_out, schema)

    # 2) Build coherence artifact referencing generated files
    cmp_md = helm_out / "comparison.md"
    audit = helm_out / "audit_bundle.json"
    delta_csv = helm_out / "delta_curve.csv"

    sources = [
        {"id": "s_cmp_md", "title": "comparison.md", "url": f"local:{cmp_md}"},
        {"id": "s_delta_csv", "title": "delta_curve.csv", "url": f"local:{delta_csv}"},
        {"id": "s_audit", "title": "audit_bundle.json", "url": f"local:{audit}"},
    ]
    claims = [
        {"id": "c1", "text": "Helmholtz comparator emits comparison and audit bundle.", "citations": ["s_cmp_md", "s_audit"]},
        {"id": "c2", "text": "Comparator emits per-step delta curve artifact.", "citations": ["s_delta_csv"]},
    ]

    artifact_path = tmp_path / "helmholtz_coherence.json"
    _write_json(
        artifact_path,
        _artifact_for_outputs(
            question="CI: Audit Helmholtz guided vs unguided comparator artifacts.",
            answer="See comparator outputs (comparison.md / delta_curve.csv) and audit bundle for traceability.",
            sources=sources,
            claims=claims,
        ),
    )

    # 3) Run coherence audit module
    coh_mod = repo / "modules" / "coherence_audit.yml"
    coh_out = tmp_path / "coh_helmholtz"
    metrics, flags = run_module(coh_mod, artifact_path, coh_out, schema)

    _assert_coherence_outputs(coh_out)
    assert "overall_pass" in flags


def test_coherence_run_tches(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"

    t_mod = repo / "modules" / "tches_compare.yml"
    t_task = repo / "tasks" / "tches_compare_sample.json"
    t_out = tmp_path / "tches_out"
    run_module(t_mod, t_task, t_out, schema)

    cmp_md = t_out / "comparison.md"
    audit = t_out / "audit_bundle.json"

    sources = [
        {"id": "s_cmp_md", "title": "comparison.md", "url": f"local:{cmp_md}"},
        {"id": "s_audit", "title": "audit_bundle.json", "url": f"local:{audit}"},
    ]
    claims = [
        {"id": "c1", "text": "TCHES compare emits comparison and audit bundle.", "citations": ["s_cmp_md", "s_audit"]},
    ]

    artifact_path = tmp_path / "tches_coherence.json"
    _write_json(
        artifact_path,
        _artifact_for_outputs(
            question="CI: Audit TCHES baseline vs lambda comparator artifacts.",
            answer="See comparison.md and audit_bundle.json for traceability.",
            sources=sources,
            claims=claims,
        ),
    )

    coh_mod = repo / "modules" / "coherence_audit.yml"
    coh_out = tmp_path / "coh_tches"
    metrics, flags = run_module(coh_mod, artifact_path, coh_out, schema)

    _assert_coherence_outputs(coh_out)
    assert "overall_pass" in flags


def test_coherence_run_quantum(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"

    q_mod = repo / "modules" / "quantum_anchor_coverage.yml"
    q_task = repo / "tasks" / "quantum_anchor_task.json"
    q_out = tmp_path / "quantum_out"
    run_module(q_mod, q_task, q_out, schema)

    rep = q_out / "report.json"
    audit = q_out / "audit_bundle.json"

    sources = [
        {"id": "s_report", "title": "report.json", "url": f"local:{rep}"},
        {"id": "s_audit", "title": "audit_bundle.json", "url": f"local:{audit}"},
    ]
    claims = [
        {"id": "c1", "text": "Quantum anchor coverage emits report and audit bundle.", "citations": ["s_report", "s_audit"]},
    ]

    artifact_path = tmp_path / "quantum_coherence.json"
    _write_json(
        artifact_path,
        _artifact_for_outputs(
            question="CI: Audit quantum anchor coverage artifacts for traceability.",
            answer="See report.json and audit_bundle.json for traceability.",
            sources=sources,
            claims=claims,
        ),
    )

    coh_mod = repo / "modules" / "coherence_audit.yml"
    coh_out = tmp_path / "coh_quantum"
    metrics, flags = run_module(coh_mod, artifact_path, coh_out, schema)

    _assert_coherence_outputs(coh_out)
    assert "overall_pass" in flags
