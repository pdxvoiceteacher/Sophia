from __future__ import annotations

import json
from pathlib import Path

from ucc.core import run_module


def test_verify_json_assertions_pipeline(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema_path = repo / "schema" / "ucc_module.schema.json"

    # 1) Create a local JSON source to validate against
    src_json = tmp_path / "comparison.json"
    src_json.write_text(
        json.dumps(
            {
                "metrics": {
                    "delta_warn_LambdaT_steps": 10,
                    "delta_alarm_LambdaT_steps": 0,
                    "delta_mean_Ppump": 0.0196,
                },
                "flags": {"improved_warn_time": True},
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    # 2) Build a coherence artifact that cites the JSON source and includes assertions in claim text
    task = {
        "coherence_artifact": {
            "id": "ci-json-assert",
            "domain": "research",
            "question": "CI: verify numeric/bool assertions against cited JSON sources.",
            "answer": "CI scaffold.",
            "sections": {
                "assumptions": "Proxy audit.",
                "limitations": "CI scaffold.",
                "uncertainty": "CI scaffold.",
                "disclosure": "CI scaffold.",
            },
            "claims": [
                {
                    "id": "c1",
                    "text": "From comparison.json: delta_warn_LambdaT_steps >= 0; delta_alarm_LambdaT_steps = 0; abs(delta_mean_Ppump) < 1; improved_warn_time = true.",
                    "citations": ["s_cmp"],
                }
            ],
            "sources": [{"id": "s_cmp", "title": "comparison.json", "url": f"local:{src_json}"}],
            "evidence": {"links": ["https://github.com/pdxvoiceteacher/CoherenceLattice"], "artifacts": []},
            "reporting_channel": {"primary": "github issues", "escalation": "maintainers"},
        }
    }

    input_json = tmp_path / "artifact.json"
    input_json.write_text(json.dumps(task, indent=2, sort_keys=True), encoding="utf-8")

    # 3) Create a tiny module YAML in tmp_path that runs verify_json_assertions
    module_yml = tmp_path / "module.yml"
    module_yml.write_text(
        "\n".join(
            [
                'ucc_version: "0.1"',
                "module:",
                '  id: "test.verify_json_assertions"',
                '  version: "0.1.0"',
                '  title: "Test verify_json_assertions"',
                '  intent: "CI pipeline test"',
                "  authors:",
                '    - name: "CI"',
                "steps:",
                "  - type: ingest_json",
                "    id: ingest",
                "  - type: verify_json_assertions",
                "    id: v",
                "    params:",
                '      sections_key: "coherence_artifact"',
                "      require_any: true",
                "      fail_on_unresolved: true",
                '      name_json: "json_assertions.json"',
                '      name_md: "json_assertions.md"',
                "  - type: emit_report",
                "    id: report",
                "    params:",
                '      report_name: "report.json"',
                "",
            ]
        ),
        encoding="utf-8",
    )

    outdir = tmp_path / "out"
    metrics, flags = run_module(module_yml, input_json, outdir, schema_path)

    assert flags.get("json_assertions_ok") is True
    assert (outdir / "json_assertions.json").exists()
    assert (outdir / "json_assertions.md").exists()
    assert (outdir / "report.json").exists()
    assert (outdir / "audit_bundle.json").exists()