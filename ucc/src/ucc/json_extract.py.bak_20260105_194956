from __future__ import annotations

import csv
import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# json path tokens: "a.b[1].c" -> ["a","b",1,"c"]
_PATH_TOKEN_RE = re.compile(r"([^.\[\]]+)|\[(\d+)\]")

_ALLOWED_TYPES = {"any", "number", "int", "bool", "string", "object"}


def _repo_root() -> Path:
    # ucc/src/ucc/json_extract.py -> ucc/src/ucc -> ucc/src -> ucc -> repo
    return Path(__file__).resolve().parents[3]


def _resolve_source_path(s: str) -> Optional[Path]:
    """
    Supports:
      - local:C:/... or local:relative/path
      - relative/path
      - absolute path

    NOTE: http(s) URLs are not fetched (returns None).
    """
    s = (s or "").strip()
    if not s:
        return None
    if s.startswith("http://") or s.startswith("https://"):
        return None
    if s.startswith("local:"):
        s = s[len("local:") :].strip()

    p = Path(s)
    if p.is_absolute():
        return p
    return _repo_root() / p


def _parse_path(path: str) -> List[Any]:
    toks: List[Any] = []
    for m in _PATH_TOKEN_RE.finditer(path.strip()):
        k = m.group(1)
        if k is not None:
            toks.append(k)
        else:
            toks.append(int(m.group(2)))
    return toks


def _get_path(obj: Any, path: str) -> Tuple[bool, Any]:
    cur = obj
    for tok in _parse_path(path):
        if isinstance(tok, int):
            if not isinstance(cur, list) or tok < 0 or tok >= len(cur):
                return False, None
            cur = cur[tok]
        else:
            if not isinstance(cur, dict) or tok not in cur:
                return False, None
            cur = cur[tok]
    return True, cur


def _coerce_value(v: Any, t: str) -> Tuple[bool, Any]:
    if t == "any":
        return True, v
    if t == "object":
        return isinstance(v, (dict, list)), v
    if t == "string":
        return isinstance(v, str), v
    if t == "bool":
        return isinstance(v, bool), v
    if t == "int":
        if isinstance(v, bool):
            return False, None
        if isinstance(v, int):
            return True, int(v)
        if isinstance(v, float) and float(v).is_integer():
            return True, int(v)
        return False, None
    if t == "number":
        if isinstance(v, bool):
            return False, None
        if isinstance(v, (int, float)):
            return True, float(v)
        return False, None
    return False, None


def extract_json_fields_task(
    task_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    config_key: str = "json_extract",
    source_json_key: str = "source_json",
    fields_key: str = "fields",
    out_json: str = "extracted_metrics.json",
    out_csv: str = "extracted_metrics.csv",
    out_md: str = "extracted_metrics.md",
    **kwargs: Any,
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    UCC step: extract fields from a JSON file.

    Input (via ingest_json):
      {
        "json_extract": {
           "source_json": "path/to/source.json"  (supports local:)
           "fields": [
              {"id":"x","path":"metrics.x","type":"number","required":true},
              ...
           ],
           "out_json": "...", "out_csv": "...", "out_md": "..."
        }
      }
    """
    outdir.mkdir(parents=True, exist_ok=True)

    cfg = task_doc.get(config_key) if config_key else task_doc
    if not isinstance(cfg, dict):
        raise ValueError(f"extract_json_fields requires dict config at key '{config_key}'")

    # allow overrides from cfg
    source_spec = str(cfg.get(source_json_key, "")).strip()
    if not source_spec:
        raise ValueError(f"extract_json_fields missing '{source_json_key}' in config")

    fields = cfg.get(fields_key, [])
    if not isinstance(fields, list) or not fields:
        raise ValueError(f"extract_json_fields requires non-empty list '{fields_key}'")

    out_json_name = str(cfg.get("out_json", out_json))
    out_csv_name = str(cfg.get("out_csv", out_csv))
    out_md_name = str(cfg.get("out_md", out_md))

    src_path = _resolve_source_path(source_spec)
    if src_path is None or not src_path.exists():
        raise FileNotFoundError(f"source_json not found or unsupported: {source_spec}")

    src = json.loads(src_path.read_text(encoding="utf-8-sig"))

    extracted: Dict[str, Any] = {}
    missing: List[str] = []
    type_errors: List[str] = []

    for f in fields:
        if not isinstance(f, dict):
            continue
        fid = str(f.get("id", "")).strip()
        jpath = str(f.get("path", "")).strip()
        ftype = str(f.get("type", "any")).strip().lower()
        required = bool(f.get("required", True))

        if not fid or not jpath:
            continue
        if ftype not in _ALLOWED_TYPES:
            raise ValueError(f"Unknown field type '{ftype}' for id={fid}. Allowed: {sorted(_ALLOWED_TYPES)}")

        ok, val = _get_path(src, jpath)
        if not ok:
            if required:
                missing.append(fid)
            continue

        ok2, val2 = _coerce_value(val, ftype)
        if not ok2:
            type_errors.append(fid)
            continue

        extracted[fid] = val2

    # Write outputs
    p_json = outdir / out_json_name
    p_csv = outdir / out_csv_name
    p_md = outdir / out_md_name

    p_json.write_text(json.dumps({"source_json": source_spec, "extracted": extracted}, indent=2, sort_keys=True), encoding="utf-8")

    # CSV
    with p_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["id", "value", "type"])
        for k in sorted(extracted.keys()):
            v = extracted[k]
            w.writerow([k, v, type(v).__name__])

    # MD
    lines = [
        "# Extracted JSON Fields",
        "",
        f"- source_json: `{source_spec}`",
        f"- extracted_count: **{len(extracted)}**",
        f"- missing_required: **{len(missing)}**",
        f"- type_errors: **{len(type_errors)}**",
        "",
        "| id | value | type |",
        "|---|---:|---|",
    ]
    for k in sorted(extracted.keys()):
        v = extracted[k]
        lines.append(f"| {k} | {v} | {type(v).__name__} |")
    if missing:
        lines += ["", "## Missing required", ""] + [f"- {x}" for x in missing]
    if type_errors:
        lines += ["", "## Type errors", ""] + [f"- {x}" for x in type_errors]
    p_md.write_text("\n".join(lines) + "\n", encoding="utf-8")

    flags = {
        "json_extract_ok": (len(missing) == 0 and len(type_errors) == 0),
        "json_extract_missing": missing,
        "json_extract_type_errors": type_errors,
    }

    metrics: Dict[str, Any] = {
        "json_extract_source": source_spec,
        "json_extract_count": len(extracted),
        "json_extract_missing_count": len(missing),
        "json_extract_type_error_count": len(type_errors),
        "json_extract_ids": sorted(extracted.keys()),
    }

    # also expose scalar values as metrics for downstream steps (safe)
    for k, v in extracted.items():
        if isinstance(v, (int, float, bool, str)):
            metrics[f"json_{k}"] = v

    return metrics, flags, [p_json, p_csv, p_md]