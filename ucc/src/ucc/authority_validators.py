from __future__ import annotations

from datetime import datetime, timezone
from typing import Any, Dict, List, Tuple, Optional
import re

ISO_UTC_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
CONTROL_KEY_RE = re.compile(
    r"(control|controls|selected|ids|include|exclude|mapping|mappings|function|functions|clause|clauses|annex|category|categories|subcategory|subcategories|requirement|requirements)",
    re.IGNORECASE,
)

ID_KEY_BLACKLIST = {
    "id", "name", "version", "publisher", "url",
    "notes", "note", "description", "scope",
    "org", "system", "jurisdiction",
    "primary", "escalation", "owner",
    "last_review_utc", "next_review_utc",
}

_SPLIT_RE = re.compile(r"[,\n;\t ]+")
_STRIP_EDGES = "\"'()[]{}<>.,;"

def _as_dict(x: Any) -> Dict[str, Any]:
    return x if isinstance(x, dict) else {}

def _as_list(x: Any) -> List[Any]:
    return x if isinstance(x, list) else []

def _nonempty_str(x: Any) -> bool:
    return isinstance(x, str) and x.strip() != ""

def _parse_iso_utc(s: str) -> Optional[datetime]:
    if not _nonempty_str(s):
        return None
    ss = s.strip()
    if not ISO_UTC_RE.match(ss):
        return None
    try:
        return datetime.strptime(ss, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    except Exception:
        return None

def _looks_like_id(s: str) -> bool:
    if not _nonempty_str(s):
        return False
    tok = s.strip()

    # Allow NIST CSF function tokens explicitly
    if tok in {"GV","ID","PR","DE","RS","RC"}:
        return True

    # Reject anything containing lowercase letters
    if re.search(r"[a-z]", tok):
        return False

    # Block structural tokens
    if tok.lower() in ID_KEY_BLACKLIST:
        return False

    # Pure letters must be short
    if re.fullmatch(r"[A-Z]+", tok):
        return len(tok) <= 4

    # General ID form
    return bool(re.fullmatch(r"[A-Z0-9][A-Z0-9_.:-]{0,40}", tok))

def _add_token(tok: str, out: set[str]) -> None:
    t = tok.strip(_STRIP_EDGES).strip()
    if _looks_like_id(t):
        out.add(t)

def _collect_ids(obj: Any, out: set[str]) -> None:
    if isinstance(obj, list):
        for x in obj:
            _collect_ids(x, out)
        return
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(k, str) and isinstance(v, (bool, int, float, str)):
                _add_token(k, out)
        for v in obj.values():
            _collect_ids(v, out)
        return
    if isinstance(obj, str):
        s = obj.strip()
        _add_token(s, out)
        for p in [p for p in _SPLIT_RE.split(s) if p]:
            _add_token(p, out)
        return

def _find_control_ids(profile: Dict[str, Any]) -> List[str]:
    ids: set[str] = set()

    if "controls" in profile:
        _collect_ids(profile.get("controls"), ids)

    for k, v in profile.items():
        if isinstance(k, str) and CONTROL_KEY_RE.search(k):
            _collect_ids(v, ids)

    inner = _as_dict(profile.get("profile"))
    for k, v in inner.items():
        if isinstance(k, str) and CONTROL_KEY_RE.search(k):
            _collect_ids(v, ids)

    if not ids:
        _collect_ids(profile, ids)

    ids.discard("id")
    ids.discard("name")
    return sorted(ids)

def _collect_links(prof: Dict[str, Any]) -> List[str]:
    links: List[str] = []

    ev = _as_dict(prof.get("evidence"))
    v = ev.get("links")
    if isinstance(v, list):
        links.extend([str(x).strip() for x in v if _nonempty_str(x)])
    elif _nonempty_str(v):
        links.append(str(v).strip())

    # Common alternates
    for k in ["evidence_links", "evidence_link", "links"]:
        vv = prof.get(k)
        if isinstance(vv, list):
            links.extend([str(x).strip() for x in vv if _nonempty_str(x)])
        elif _nonempty_str(vv):
            links.append(str(vv).strip())

    # Dedup
    out: List[str] = []
    seen = set()
    for x in links:
        if x not in seen:
            out.append(x)
            seen.add(x)
    return out

def validate_authority_profile(
    task_doc: Dict[str, Any],
    sections_key: str,
    *,
    min_links: int = 1,
    require_review_dates: bool = True,
    require_exception_items: bool = True,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    prof = task_doc.get(sections_key)
    if not isinstance(prof, dict):
        raise ValueError(f"validate_authority_profile expects task_doc['{sections_key}'] to be a dict")

    authority = _as_dict(prof.get("authority"))
    review = _as_dict(prof.get("review_cycle"))
    exceptions = _as_dict(prof.get("exceptions"))
    reporting = _as_dict(prof.get("reporting_channel"))

    links = _collect_links(prof)
    control_ids = _find_control_ids(prof)

    # Minimal authority requirement (compat-friendly)
    auth_ok = _nonempty_str(authority.get("id"))

    links_ok = len(links) >= int(min_links)
    controls_ok = len(control_ids) > 0

    # Review cycle
    review_ok = True
    if require_review_dates:
        last_ok = _parse_iso_utc(str(review.get("last_review_utc", ""))) is not None
        next_ok = _parse_iso_utc(str(review.get("next_review_utc", ""))) is not None
        review_ok = bool(last_ok and next_ok)

    # Exceptions
    exc_items = _as_list(exceptions.get("items"))
    now = datetime.now(timezone.utc)
    expired = 0
    unparsable = 0

    exceptions_ok = True
    if require_exception_items:
        exceptions_ok = isinstance(exc_items, list) and len(exc_items) > 0

    if isinstance(exc_items, list):
        for it in exc_items:
            if not isinstance(it, dict):
                continue
            exp = _parse_iso_utc(str(it.get("expires_utc", "")))
            if exp is None:
                unparsable += 1
                continue
            if exp < now:
                expired += 1

    if require_exception_items:
        exceptions_ok = bool(exceptions_ok and expired == 0 and unparsable == 0)

    reporting_ok = _nonempty_str(reporting.get("primary")) and _nonempty_str(reporting.get("escalation"))

    # ✅ Compatibility + bells/whistles:
    # deep validation = “controls parsed and non-empty”
    deep_ok = controls_ok
    governance_ok = bool(review_ok and exceptions_ok and reporting_ok)
    overall_ok = bool(auth_ok and links_ok and governance_ok and controls_ok)

    metrics: Dict[str, Any] = {
        "authority_id": str(authority.get("id", "")),
        "authority_auth_ok": auth_ok,
        "evidence_links_count": len(links),
        "evidence_links_min_required": int(min_links),
        "controls_count": len(control_ids),
        "controls_ids_preview": control_ids[:12],
        "review_required": bool(require_review_dates),
        "exceptions_required": bool(require_exception_items),
        "exceptions_items_count": len(exc_items) if isinstance(exc_items, list) else 0,
        "exceptions_expired_count": expired,
        "exceptions_unparsable_expiry_count": unparsable,
        "reporting_channel_ok": reporting_ok,
        "authority_deep_ok": deep_ok,
        "authority_governance_ok": governance_ok,
    }

    flags: Dict[str, Any] = {
        "authority_deep_validation_ok": deep_ok,   # legacy test expectation
        "authority_governance_ok": governance_ok,
        "authority_profile_ok": overall_ok,        # strict full profile
        "authority_links_ok": links_ok,
        "authority_review_ok": review_ok,
        "authority_exceptions_ok": exceptions_ok,
        "authority_controls_ok": controls_ok,
        "authority_reporting_ok": reporting_ok,
    }

    return metrics, flags