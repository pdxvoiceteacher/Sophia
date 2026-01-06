from __future__ import annotations

import csv
import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

HTTP_RE = re.compile(r"^https?://", re.IGNORECASE)

# -----------------------------
# Utilities
# -----------------------------
def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]

def _load_json_path(p: Path) -> Any:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def _read_authorities_index() -> Dict[str, Any]:
    idx = _repo_root() / "ucc" / "authorities" / "index.json"
    if not idx.exists():
        return {"authorities": []}
    d = _load_json_path(idx)
    # tolerate legacy key "packs"
    if "authorities" not in d and "packs" in d:
        d["authorities"] = d["packs"]
    if "authorities" not in d:
        d["authorities"] = []
    return d

def _authority_by_id() -> Dict[str, Dict[str, Any]]:
    idx = _read_authorities_index()
    out: Dict[str, Dict[str, Any]] = {}
    for a in idx.get("authorities", []):
        if isinstance(a, dict) and "id" in a:
            out[str(a["id"])] = a
    return out

def _truthy(s: str) -> bool:
    return str(s).strip().lower() in {"1", "true", "yes", "y", "on"}

def _split_links(val: str) -> List[str]:
    if val is None:
        return []
    s = str(val).strip()
    if not s:
        return []
    # allow ';' or ',' separated
    parts = re.split(r"[;,]\s*", s)
    return [p.strip() for p in parts if p.strip()]

def _pick(row: Dict[str, Any], keys: List[str]) -> str:
    for k in keys:
        if k in row and str(row[k]).strip():
            return str(row[k]).strip()
    return ""

def _resolve_pack_path(authority_entry: Dict[str, Any]) -> Optional[Path]:
    p = authority_entry.get("path") or authority_entry.get("pack_path") or authority_entry.get("pack")
    if not p:
        return None
    p = str(p)
    # allow "ucc/authorities/..." relative
    root = _repo_root()
    pp = Path(p)
    if pp.is_absolute():
        return pp
    return root / pp

def _collect_ids_from_pack(pack_doc: Any) -> set[str]:
    """
    Best-effort: recursively collect plausible ID strings from pack.json.
    Keeps it permissive for IDs-only packs.
    """
    ids: set[str] = set()

    def rec(x: Any):
        if isinstance(x, dict):
            for k, v in x.items():
                rec(v)
        elif isinstance(x, list):
            for v in x:
                rec(v)
        elif isinstance(x, str):
            s = x.strip()
            # keep typical control id patterns
            if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.:-]*", s) and len(s) <= 64:
                ids.add(s)

    rec(pack_doc)
    return ids

# -----------------------------
# Table validator
# -----------------------------
def validate_mapping_table_task(
    rows: List[Dict[str, Any]],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    strict: bool = False,
    require_review: bool = True,
    require_expiry: bool = True,
    default_enforced: bool = False,
    evidence_col: str = "evidence",
    **kwargs: Any,
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    Input: rows from ingest_csv (list[dict]).
    Validates:
      - from_pack/to_pack exist in authorities index
      - optional: IDs appear in packs (best-effort)
      - evidence rules:
          * if strict AND enforced -> require at least one http(s) URL
          * if not strict OR not enforced -> local:NA allowed
      - review/expiry present (if required)
    """
    outdir.mkdir(parents=True, exist_ok=True)

    auth = _authority_by_id()

    # column name flex
    FROM_PACK_KEYS = ["from_pack", "from_authority", "from_standard", "from_framework"]
    TO_PACK_KEYS   = ["to_pack", "to_authority", "to_standard", "to_framework"]
    FROM_ID_KEYS   = ["from_id", "from_control", "from_control_id", "from_req", "from_requirement"]
    TO_ID_KEYS     = ["to_id", "to_control", "to_control_id", "to_req", "to_requirement"]
    ENF_KEYS       = ["enforced", "strict", "enforced_mapping"]
    REVIEW_KEYS    = ["review_utc", "last_review_utc", "review_date"]
    EXP_KEYS       = ["expires_utc", "expiry_utc", "expires", "expiry_date"]

    missing_packs = 0
    missing_ids = 0
    evidence_bad = 0
    review_bad = 0
    expiry_bad = 0
    checked = 0

    # cache pack id sets
    pack_ids_cache: Dict[str, set[str]] = {}

    def pack_ids(pack_id: str) -> set[str]:
        if pack_id in pack_ids_cache:
            return pack_ids_cache[pack_id]
        entry = auth.get(pack_id, {})
        p = _resolve_pack_path(entry) if entry else None
        if p and p.exists():
            doc = _load_json_path(p)
            ids = _collect_ids_from_pack(doc)
        else:
            ids = set()
        pack_ids_cache[pack_id] = ids
        return ids

    for r in rows:
        if not isinstance(r, dict):
            continue
        checked += 1
        fp = _pick(r, FROM_PACK_KEYS)
        tp = _pick(r, TO_PACK_KEYS)
        fid = _pick(r, FROM_ID_KEYS)
        tid = _pick(r, TO_ID_KEYS)

        if fp not in auth or tp not in auth:
            missing_packs += 1

        # best-effort ID existence check (only if pack doc exists and has ids)
        if fp in auth and fid:
            ids = pack_ids(fp)
            if ids and fid not in ids:
                missing_ids += 1
        if tp in auth and tid:
            ids = pack_ids(tp)
            if ids and tid not in ids:
                missing_ids += 1

        enforced = default_enforced
        enf_raw = _pick(r, ENF_KEYS)
        if enf_raw:
            enforced = _truthy(enf_raw)

        links = _split_links(r.get(evidence_col, ""))

        if strict and enforced:
            # strict-enforced must have at least one http(s) link
            if not any(HTTP_RE.match(u or "") for u in links):
                evidence_bad += 1
        else:
            # drafts can use local:NA
            pass

        if require_review:
            rv = _pick(r, REVIEW_KEYS)
            if not rv:
                review_bad += 1

        if require_expiry:
            ex = _pick(r, EXP_KEYS)
            if not ex:
                expiry_bad += 1

    flags = {
        "mapping_table_ok": (missing_packs == 0 and missing_ids == 0 and evidence_bad == 0 and review_bad == 0 and expiry_bad == 0),
        "mapping_missing_packs": missing_packs,
        "mapping_missing_ids": missing_ids,
        "mapping_evidence_bad": evidence_bad,
        "mapping_review_missing": review_bad,
        "mapping_expiry_missing": expiry_bad,
        "mapping_checked_rows": checked,
    }

    metrics = {
        "mapping_checked_rows": checked,
        "mapping_missing_packs": missing_packs,
        "mapping_missing_ids": missing_ids,
        "mapping_evidence_bad": evidence_bad,
        "mapping_review_missing": review_bad,
        "mapping_expiry_missing": expiry_bad,
    }

    # Write summary
    p_json = outdir / "mapping_table_validate.json"
    p_md = outdir / "mapping_table_validate.md"
    p_json.write_text(json.dumps({"metrics": metrics, "flags": flags}, indent=2, sort_keys=True), encoding="utf-8")
    p_md.write_text(
        "# Mapping Table Validation\n\n"
        f"- checked_rows: **{checked}**\n"
        f"- missing_packs: **{missing_packs}**\n"
        f"- missing_ids: **{missing_ids}**\n"
        f"- evidence_bad: **{evidence_bad}**\n"
        f"- review_missing: **{review_bad}**\n"
        f"- expiry_missing: **{expiry_bad}**\n"
        f"- ok: **{flags['mapping_table_ok']}**\n",
        encoding="utf-8"
    )

    return metrics, flags, [p_json, p_md]

# -----------------------------
# Index validator (registry walker)
# -----------------------------
def validate_mapping_index_task(
    task_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    index_key: str = "mappings",
    strict: bool = False,
    **kwargs: Any,
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    Validates mapping registry index.json:
      - entries have id/path/enforced
      - file exists
      - if enforced OR strict -> run validate_mapping_table_task on CSV
    """
    outdir.mkdir(parents=True, exist_ok=True)

    idx = task_doc
    # tolerate older key names
    entries = idx.get(index_key)
    if entries is None:
        entries = idx.get("tables") or idx.get("mappings") or []

    if not isinstance(entries, list):
        raise ValueError("validate_mapping_index requires a list at key 'mappings' (or 'tables')")

    missing_files = 0
    bad_entries = 0
    enforced_failed = 0
    checked = 0

    root = _repo_root()

    for e in entries:
        if not isinstance(e, dict):
            bad_entries += 1
            continue
        mid = str(e.get("id", "")).strip()
        path = str(e.get("path", "")).strip()
        enforced = bool(e.get("enforced", False))
        if not mid or not path:
            bad_entries += 1
            continue

        p = Path(path)
        if not p.is_absolute():
            p = root / p
        if not p.exists():
            missing_files += 1
            continue

        checked += 1

        # if enforced or strict, validate table content
        if enforced or strict:
            # must be CSV mapping table
            with p.open("r", encoding="utf-8-sig", newline="") as f:
                reader = csv.DictReader(f)
                rows = list(reader)
            _, fl, _ = validate_mapping_table_task(rows, outdir / f"m_{mid}", thresholds, strict=strict)
            if not fl.get("mapping_table_ok", False):
                enforced_failed += 1

    flags = {
        "mapping_index_ok": (missing_files == 0 and bad_entries == 0 and enforced_failed == 0),
        "mapping_index_missing_files": missing_files,
        "mapping_index_bad_entries": bad_entries,
        "mapping_index_enforced_failed": enforced_failed,
        "mapping_index_checked": checked,
    }
    metrics = dict(flags)

    p_json = outdir / "mapping_index_validate.json"
    p_md = outdir / "mapping_index_validate.md"
    p_json.write_text(json.dumps({"metrics": metrics, "flags": flags}, indent=2, sort_keys=True), encoding="utf-8")
    p_md.write_text(
        "# Mapping Index Validation\n\n"
        f"- checked: **{checked}**\n"
        f"- missing_files: **{missing_files}**\n"
        f"- bad_entries: **{bad_entries}**\n"
        f"- enforced_failed: **{enforced_failed}**\n"
        f"- ok: **{flags['mapping_index_ok']}**\n",
        encoding="utf-8",
    )

    return metrics, flags, [p_json, p_md]