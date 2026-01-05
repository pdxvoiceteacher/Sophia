from __future__ import annotations

import csv
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Tuple

from .mapping_validators import validate_mapping_table_task

def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]

def _read_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))

def _load_csv_rows(path: Path) -> List[Dict[str, str]]:
    with path.open("r", newline="", encoding="utf-8-sig") as f:
        r = csv.DictReader(f)
        return list(r)

_safe_re = re.compile(r"[^A-Za-z0-9_.-]+")

def _safe_name(s: str) -> str:
    return _safe_re.sub("_", s)

def validate_mapping_index_task(
    index_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any] | None = None,
    *,
    registry_index_path: str = "ucc/authorities/index.json",
    enforced_key: str = "enforced",
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    thresholds = thresholds or {}
    outdir.mkdir(parents=True, exist_ok=True)

    repo = _repo_root()

    enforced = index_doc.get(enforced_key, [])
    if not isinstance(enforced, list) or len(enforced) == 0:
        raise ValueError(f"validate_mapping_index requires index_doc['{enforced_key}'] list")

    total = 0
    ok = 0
    failed: List[str] = []
    out_files: List[Path] = []

    for item in enforced:
        if not isinstance(item, dict):
            continue
        rel = str(item.get("path", "")).strip()
        mode = str(item.get("mode", "strict")).strip().lower()
        if not rel:
            continue

        csv_path = (repo / rel).resolve()
        if not csv_path.exists():
            # allow paths starting with "ucc/"
            rel2 = rel.split("ucc/")[-1]
            csv_path = (repo / "ucc" / rel2).resolve()

        if not csv_path.exists():
            failed.append(rel)
            total += 1
            continue

        rows = _load_csv_rows(csv_path)
        sub = outdir / _safe_name(csv_path.stem)
        sub.mkdir(parents=True, exist_ok=True)

        params: Dict[str, Any] = {
            "registry_index_path": registry_index_path,
            "require_review_utc": True,
            "require_expires_utc": True,
            "enforce_not_expired": True,
            "allow_local_na": True,
        }
        if mode == "loose":
            params["require_review_utc"] = False
            params["require_expires_utc"] = False

        m, fl, outs = validate_mapping_table_task(rows, sub, thresholds, **params)
        out_files.extend(outs)

        total += 1
        if fl.get("mapping_table_ok"):
            ok += 1
        else:
            failed.append(rel)

    metrics = {
        "mapping_index_total": total,
        "mapping_index_ok": ok,
        "mapping_index_failed": len(failed),
        "mapping_index_failed_paths": failed,
        "registry_index_path": registry_index_path,
        "enforced_key": enforced_key,
    }
    flags = {
        "mapping_index_ok": (ok == total and total > 0),
    }
    return metrics, flags, out_files