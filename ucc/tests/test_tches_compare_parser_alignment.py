from __future__ import annotations

from pathlib import Path
import json
import math
import re

from ucc.core import run_module


def _close(a: float, b: float, abs_tol: float = 1e-6, rel_tol: float = 1e-6) -> bool:
    return abs(a - b) <= max(abs_tol, rel_tol * max(abs(a), abs(b), 1.0))


def _find_float_md(md: str, label_regex: str) -> float:
    """
    Find a bolded float like **0.01964** near a label phrase.
    """
    m = re.search(label_regex + r".*?\*\*([0-9.eE+-]+)\*\*", md, re.IGNORECASE | re.DOTALL)
    if not m:
        raise AssertionError(f"Missing numeric markdown for pattern: {label_regex}")
    return float(m.group(1))


def test_tches_compare_parser_matches_markdown(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"

    # 1) Run comparator to tmp
    t_mod = repo / "modules" / "tches_compare.yml"
    t_task = repo / "tasks" / "tches_compare_sample.json"
    t_out = tmp_path / "tches_compare_out"
    run_module(t_mod, t_task, t_out, schema)

    cmp_json = t_out / "comparison.json"
    cmp_md = t_out / "comparison.md"
    assert cmp_json.exists(), "tches_compare must emit comparison.json"
    assert cmp_md.exists(), "tches_compare must emit comparison.md"

    # Detect where the metrics live in comparison.json
    doc = json.loads(cmp_json.read_text(encoding="utf-8-sig"))
    if isinstance(doc, dict) and "metrics" in doc and isinstance(doc["metrics"], dict):
        base = "metrics"
    else:
        base = ""  # assume flat dict of metrics

    def p(k: str) -> str:
        return f"{base}.{k}" if base else k

    # 2) Run parser step (extract_json_fields) on that comparison.json
    extract_task = {
        "json_extract": {
            "source_json": str(cmp_json),
            "fields": [
                {"id": "delta_warn_LambdaT_steps", "path": p("delta_warn_LambdaT_steps"), "type": "int", "required": True},
                {"id": "delta_alarm_LambdaT_steps", "path": p("delta_alarm_LambdaT_steps"), "type": "int", "required": True},
                {"id": "delta_mean_Ppump", "path": p("delta_mean_Ppump"), "type": "number", "required": True},
                {"id": "delta_mean_Qch", "path": p("delta_mean_Qch"), "type": "number", "required": True},
            ],
            "out_json": "extracted_metrics.json",
            "out_csv": "extracted_metrics.csv",
            "out_md": "extracted_metrics.md",
        }
    }

    task_path = tmp_path / "tches_extract_task.json"
    task_path.write_text(json.dumps(extract_task, indent=2), encoding="utf-8")

    extract_mod = repo / "modules" / "json_extract_fields.yml"
    extract_out = tmp_path / "extract_out"
    m2, f2 = run_module(extract_mod, task_path, extract_out, schema)
    assert f2.get("json_extract_ok") is True

    extracted = json.loads((extract_out / "extracted_metrics.json").read_text(encoding="utf-8"))["extracted"]
    dw = int(extracted["delta_warn_LambdaT_steps"])
    da = int(extracted["delta_alarm_LambdaT_steps"])
    dp = float(extracted["delta_mean_Ppump"])
    dq = float(extracted["delta_mean_Qch"])

    # 3) Verify comparison.md matches the extracted numbers
    md = cmp_md.read_text(encoding="utf-8", errors="ignore")

    # Rows in the summary table are the most stable anchor.
    m = re.search(r"\|\s*warn_LambdaT_steps\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|", md)
    assert m, "Missing warn_LambdaT_steps table row"
    assert int(m.group(3)) == dw

    m = re.search(r"\|\s*alarm_LambdaT_steps\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|", md)
    assert m, "Missing alarm_LambdaT_steps table row"
    assert int(m.group(3)) == da

    # Prefer the prose lines if present; otherwise fall back to the table rows.
    try:
        md_dp = _find_float_md(md, r"delta mean pump power")
    except AssertionError:
        m = re.search(r"\|\s*mean_Ppump\s*\|\s*([0-9.eE+-]+)\s*\|\s*([0-9.eE+-]+)\s*\|\s*([0-9.eE+-]+)\s*\|", md)
        assert m, "Missing mean_Ppump table row"
        md_dp = float(m.group(3))

    try:
        md_dq = _find_float_md(md, r"delta mean chiller load")
    except AssertionError:
        m = re.search(r"\|\s*mean_Qch\s*\|\s*([0-9.eE+-]+)\s*\|\s*([0-9.eE+-]+)\s*\|\s*([0-9.eE+-]+)\s*\|", md)
        assert m, "Missing mean_Qch table row"
        md_dq = float(m.group(3))

    assert _close(md_dp, dp, abs_tol=1e-6, rel_tol=1e-6), (md_dp, dp)
    assert _close(md_dq, dq, abs_tol=1e-6, rel_tol=1e-6), (md_dq, dq)
