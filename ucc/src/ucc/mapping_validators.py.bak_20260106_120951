from __future__ import annotations

import csv
import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Set

HTTP_RE = re.compile(r"^https?://", re.IGNORECASE)


def _repo_root() -> Path:
    # .../ucc/src/ucc/mapping_validators.py -> repo root
    return Path(__file__).resolve().parents[3]


def _load_json_path(p: Path) -> Any:
    return json.loads(p.read_text(encoding="utf-8-sig"))


def _read_authorities_index() -> Dict[str, Any]:
    idx = _repo_root() / "ucc" / "authorities" / "index.json"
    if not idx.exists():
        return {"authorities": []}
    d = _load_json_path(idx)
    # Back-compat: {"packs":[...]}
    if "authorities" not in d and "packs" in d:
        d["authorities"] = d["packs"]
    if "authorities" not in d or not isinstance(d["authorities"], list):
        d["authorities"] = []
    return d


def _authority_by_id() -> Dict[str, Dict[str, Any]]:
    idx = _read_authorities_index()
    out: Dict[str, Dict[str, Any]] = {}
    for a in idx.get("authorities", []):
        if isinstance(a, dict) and "id" in a:
            out[str(a["id"])] = a
    return out


def _truthy(x: Any) -> bool:
    return str(x).strip().lower() in {"1", "true", "yes", "y", "on"}


def _split_links(val: Any) -> List[str]:
    if val is None:
        return []
    s = str(val).strip()
    if not s:
        return []
    parts = re.split(r"[;,]\s*", s)
    return [p.strip() for p in parts if p.strip()]


def _row_lc(row: Dict[str, Any]) -> Dict[str, Any]:
    return {str(k).strip().lower(): v for k, v in row.items()}


def _pick(row: Dict[str, Any], keys: List[str]) -> str:
    r = _row_lc(row)
    for k in keys:
        kk = k.lower()
        if kk in r and str(r[kk]).strip():
            return str(r[kk]).strip()
    return ""


def _resolve_pack_path(authority_entry: Dict[str, Any]) -> Optional[Path]:
    p = authority_entry.get("path") or authority_entry.get("pack_path") or authority_entry.get("pack")
    if not p:
        return None
    pp = Path(str(p))
    if pp.is_absolute():
        return pp
    return _repo_root() / pp


def _collect_ids_from_pack(pack_doc: Any) -> Set[str]:
    ids: Set[str] = set()

    def rec(x: Any) -> None:
        if isinstance(x, dict):
            for k, v in x.items():
                if k in {"id", "control_id", "req_id", "requirement_id", "practice_id", "criteria_id"} and isinstance(v, str):
                    ids.add(v.strip())
                rec(v)
        elif isinstance(x, list):
            for v in x:
                rec(v)

    if isinstance(pack_doc, dict):
        rec(pack_doc)

    out: Set[str] = set()
    for s in ids:
        t = s.strip()
        if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.:-]*", t):
            out.add(t)
    return out


def _row_evidence_links(row: Dict[str, Any], evidence_col: str) -> List[str]:
    candidates = [evidence_col, "evidence", "evidence_links", "links", "urls", "url", "evidence_url"]
    for c in candidates:
        v = _pick(row, [c])
        if v:
            return _split_links(v)
    return []


def validate_mapping_table_task(
    rows: List[Dict[str, Any]],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    strict: bool = False,
    default_enforced: bool = False,
    evidence_col: str = "evidence",
    enforce_id_existence: bool = False,
    name_json: str = "mapping_validation.json",
    name_md: str = "mapping_validation.md",
    name_csv: str = "mapping_validation.csv",
    **kwargs: Any,
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    UCC step: validate_mapping_table

    Ensures:
      - packs referenced exist in ucc/authorities/index.json
      - (optional) IDs exist in pack.json (IDs-only packs ok)
      - strict+enforced requires review+expiry and http(s) evidence
    Writes:
      - mapping_validation.md
      - mapping_validation.csv
      - mapping_validation.json
    """
    outdir.mkdir(parents=True, exist_ok=True)
    auth = _authority_by_id()

    FROM_PACK = ["from_pack", "source_pack", "src_pack", "pack_from", "from_authority", "source_authority", "from_framework", "source_framework", "from"]
    TO_PACK   = ["to_pack", "target_pack", "dst_pack", "dest_pack", "pack_to", "to_authority", "target_authority", "to_framework", "target_framework", "to"]
    FROM_ID   = ["from_id", "source_id", "src_id", "from_control", "from_control_id", "from_requirement", "from_req", "from_practice", "from_practice_id"]
    TO_ID     = ["to_id", "target_id", "dst_id", "to_control", "to_control_id", "to_requirement", "to_req", "to_practice", "to_practice_id"]
    ENF       = ["enforced", "enforced_mapping", "strict", "is_enforced"]
    REVIEW    = ["review_utc", "last_review_utc", "review_date", "reviewed_utc", "last_review"]
    EXP       = ["expires_utc", "expiry_utc", "expires", "expiry_date", "expires_at", "expiry"]

    missing_packs = 0
    missing_ids = 0
    evidence_bad = 0
    review_missing = 0
    expiry_missing = 0
    checked = 0

    issues: List[str] = []
    pack_ids_cache: Dict[str, Set[str]] = {}

    def pack_ids(pack_id: str) -> Set[str]:
        if pack_id in pack_ids_cache:
            return pack_ids_cache[pack_id]
        entry = auth.get(pack_id, {})
        p = _resolve_pack_path(entry) if entry else None
        ids: Set[str] = set()
        if p and p.exists():
            ids = _collect_ids_from_pack(_load_json_path(p))
        pack_ids_cache[pack_id] = ids
        return ids

    for r in rows:
        if not isinstance(r, dict):
            continue
        if not any(str(v).strip() for v in r.values()):
            continue

        checked += 1
        fp = _pick(r, FROM_PACK)
        tp = _pick(r, TO_PACK)
        fid = _pick(r, FROM_ID)
        tid = _pick(r, TO_ID)

        if fp not in auth or tp not in auth:
            missing_packs += 1
            issues.append(f"missing_pack: from={fp!r} to={tp!r}")

        enforced = default_enforced or _truthy(_pick(r, ENF))
        enforce_ids_now = enforce_id_existence or enforced or strict

        if enforce_ids_now:
            if fp in auth and fid:
                ids = pack_ids(fp)
                if ids and fid not in ids:
                    missing_ids += 1
                    issues.append(f"missing_id: {fp}:{fid}")
            if tp in auth and tid:
                ids = pack_ids(tp)
                if ids and tid not in ids:
                    missing_ids += 1
                    issues.append(f"missing_id: {tp}:{tid}")

        if enforced or strict:
            if not _pick(r, REVIEW):
                review_missing += 1
                issues.append("missing_review_date")
            if not _pick(r, EXP):
                expiry_missing += 1
                issues.append("missing_expiry_date")

        links = _row_evidence_links(r, evidence_col)
        links_norm = [x.strip() for x in links if x.strip()]

        if enforced and strict:
            links_norm = [x for x in links_norm if x.lower() not in {"local:na", "na", "n/a"}]
            if not any(HTTP_RE.match(u) for u in links_norm):
                evidence_bad += 1
                issues.append("bad_evidence: requires http(s) for enforced+strict")

    ok = (missing_packs == 0 and missing_ids == 0 and evidence_bad == 0 and review_missing == 0 and expiry_missing == 0)

    flags: Dict[str, Any] = {
        "mapping_table_ok": bool(ok),
        "mapping_missing_packs": missing_packs,
        "mapping_missing_ids": missing_ids,
        "mapping_evidence_bad": evidence_bad,
        "mapping_review_missing": review_missing,
        "mapping_expiry_missing": expiry_missing,
        "mapping_checked_rows": checked,
    }
    metrics: Dict[str, Any] = dict(flags)

    p_json = outdir / name_json
    p_md = outdir / name_md
    p_csv = outdir / name_csv

    p_json.write_text(json.dumps({"metrics": metrics, "flags": flags, "issues": issues}, indent=2, sort_keys=True), encoding="utf-8")

    md_lines = [
        "# Mapping Table Validation",
        "",
        f"- checked_rows: **{checked}**",
        f"- missing_packs: **{missing_packs}**",
        f"- missing_ids: **{missing_ids}**",
        f"- evidence_bad: **{evidence_bad}**",
        f"- review_missing: **{review_missing}**",
        f"- expiry_missing: **{expiry_missing}**",
        f"- ok: **{ok}**",
        "",
    ]
    if issues:
        md_lines.append("## Issues")
        for it in issues[:200]:
            md_lines.append(f"- {it}")
        if len(issues) > 200:
            md_lines.append(f"- ...(truncated; {len(issues)} total)")
        md_lines.append("")
    p_md.write_text("\n".join(md_lines), encoding="utf-8")

    with p_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["issue"])
        if issues:
            for it in issues:
                w.writerow([it])
        else:
            w.writerow(["OK"])

    return metrics, flags, [p_json, p_md, p_csv]


def validate_mapping_index_task(
    index_doc: Dict[str, Any],
    outdir: Path,
    thresholds: Dict[str, Any],
    *,
    registry_index_path: Optional[str] = None,
    enforced_key: str = "enforced",
    drafts_key: str = "drafts",
    require_http_urls: bool = False,
    strict_enforced_no_local_na: bool = False,
    out_json: Optional[str] = None,
    out_md: Optional[str] = None,
    name_json: str = "mapping_index_check.json",
    name_md: str = "mapping_index_check.md",
    **kwargs: Any,
) -> Tuple[Dict[str, Any], Dict[str, Any], List[Path]]:
    """
    UCC step: validate_mapping_index
    Input: parsed JSON of ucc/authorities/mappings/index.json (ingest_json)
    Output: mapping_index_check.json + mapping_index_check.md (names can be overridden)
    """
    outdir.mkdir(parents=True, exist_ok=True)

    metrics: Dict[str, Any] = {}
    flags: Dict[str, Any] = {}
    issues: List[str] = []

    if not isinstance(index_doc, dict):
        flags["mapping_index_ok"] = False
        metrics["mapping_index_error"] = "index must be a JSON object"
        p_json = outdir / (out_json or name_json)
        p_md = outdir / (out_md or name_md)
        p_json.write_text(json.dumps({"metrics": metrics, "flags": flags}, indent=2, sort_keys=True), encoding="utf-8")
        p_md.write_text("# Mapping Index Validation\n\n- ok: **False**\n\nReason: index not an object\n", encoding="utf-8")
        return metrics, flags, [p_json, p_md]

    base_dir = None
    if registry_index_path:
        rp = Path(str(registry_index_path))
        base_dir = rp.parent if rp.suffix.lower() == ".json" else rp
    if base_dir is None:
        base_dir = _repo_root() / "ucc" / "authorities" / "mappings"

    entries: List[Tuple[str, Dict[str, Any]]] = []
    for group, key in [("enforced", enforced_key), ("drafts", drafts_key)]:
        xs = index_doc.get(key, [])
        if xs is None:
            continue
        if not isinstance(xs, list):
            issues.append(f"bad_shape:{key} not a list")
            continue
        for it in xs:
            if isinstance(it, dict):
                entries.append((group, it))
            else:
                issues.append(f"bad_shape:{key} contains non-object")

    missing_path = 0
    missing_file = 0
    bad_path = 0
    bad_url = 0

    def resolve_mapping_csv(p: str) -> Path:
        s = str(p).strip()
        rr = _repo_root()
        candidates = [
            rr / s,
            rr / s.replace("ucc/", ""),
            rr / ("ucc" / s),
            rr / ("ucc" / s.replace("ucc/", "")),
            base_dir / s,
            base_dir / s.replace("ucc/", ""),
        ]
        for c in candidates:
            if c.exists():
                return c
        return candidates[0]

    for group, it in entries:
        p = it.get("path")
        if not p:
            missing_path += 1
            continue

        ps = str(p).strip()
        if not ps.lower().endswith(".csv"):
            bad_path += 1
            issues.append(f"bad_path_ext:{ps}")

        csvp = resolve_mapping_csv(ps)
        if not csvp.exists():
            missing_file += 1
            issues.append(f"missing_file:{ps}")

        ev = ""
        if isinstance(it.get("evidence_url"), str):
            ev = it["evidence_url"].strip()
        elif isinstance(it.get("url"), str):
            ev = it["url"].strip()

        if strict_enforced_no_local_na and group == "enforced":
            if (not ev) or ev.lower() in {"local:na", "na", "n/a"}:
                bad_url += 1
                issues.append(f"bad_url:enforced_requires_http:{ps}")
            elif require_http_urls and (not HTTP_RE.match(ev)):
                bad_url += 1
                issues.append(f"bad_url:not_http:{ev}")

        if require_http_urls and ev and (not HTTP_RE.match(ev)):
            bad_url += 1
            issues.append(f"bad_url:not_http:{ev}")

    ok = (missing_path == 0 and missing_file == 0 and bad_path == 0 and bad_url == 0 and not any(x.startswith("bad_shape") for x in issues))
    flags["mapping_index_ok"] = bool(ok)

    metrics.update({
        "mapping_index_entries": len(entries),
        "mapping_index_missing_path": missing_path,
        "mapping_index_missing_file": missing_file,
        "mapping_index_bad_path": bad_path,
        "mapping_index_bad_url": bad_url,
        "mapping_index_issues": len(issues),
    })

    p_json = outdir / (out_json or name_json)
    p_md = outdir / (out_md or name_md)
    p_json.write_text(json.dumps({"metrics": metrics, "flags": flags, "issues": issues}, indent=2, sort_keys=True), encoding="utf-8")

    md = ["# Mapping Index Validation", "", f"- ok: **{ok}**", ""]
    if issues:
        md.append("## Issues")
        md.extend([f"- {x}" for x in issues[:200]])
        if len(issues) > 200:
            md.append(f"- ...(truncated; {len(issues)} total)")
        md.append("")
    p_md.write_text("\n".join(md), encoding="utf-8")

    return metrics, flags, [p_json, p_md]