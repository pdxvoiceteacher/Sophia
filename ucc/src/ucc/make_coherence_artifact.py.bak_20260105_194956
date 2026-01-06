from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


_HEADING_RE = re.compile(r"^(#{1,6})\s+(.+?)\s*$")


def _utc_now() -> datetime:
    return datetime.now(timezone.utc)


def _iso_z(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _slug(s: str) -> str:
    s = s.strip().lower()
    s = re.sub(r"[^a-z0-9]+", "_", s)
    return s.strip("_")


def parse_markdown_sections(md_text: str) -> Dict[str, str]:
    """
    Parses markdown headings into a {section_slug: section_text} dict.
    Uses any heading level (#..######). Content is raw text between headings.
    """
    lines = md_text.splitlines()
    sections: Dict[str, List[str]] = {}
    cur_key = "body"
    sections[cur_key] = []

    for ln in lines:
        m = _HEADING_RE.match(ln)
        if m:
            title = m.group(2)
            cur_key = _slug(title)
            if cur_key not in sections:
                sections[cur_key] = []
            continue
        sections[cur_key].append(ln)

    # join and trim
    out: Dict[str, str] = {}
    for k, v in sections.items():
        text = "\n".join(v).strip()
        if text:
            out[k] = text
    return out

def load_perturbations_json(path: Path) -> List[Dict[str, Any]]:
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    if isinstance(data, dict) and "perturbations" in data:
        data = data["perturbations"]
    if not isinstance(data, list):
        return []
    out: List[Dict[str, Any]] = []
    for x in data:
        if isinstance(x, dict):
            out.append(x)
    return out


def load_claims_csv(path: Path) -> List[Dict[str, Any]]:
    """
    Expected columns:
      claim_id, claim_text, citations
    citations is optional; if present, use ';' separated source ids.
    """
    claims: List[Dict[str, Any]] = []
    with path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            cid = (row.get("claim_id") or "").strip() or f"c{len(claims)+1}"
            ctext = (row.get("claim_text") or "").strip()
            cits_raw = (row.get("citations") or "").strip()
            cits = [x.strip() for x in cits_raw.split(";") if x.strip()] if cits_raw else []
            if not ctext:
                continue
            claims.append({"id": cid, "text": ctext, "citations": cits})
    return claims


def load_sources_csv(path: Path) -> List[Dict[str, Any]]:
    """
    Expected columns:
      id, title, url, path, retrieved_utc
    - url or path may be blank; if path exists, sha256 is computed.
    """
    sources: List[Dict[str, Any]] = []
    with path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            sid = (row.get("id") or "").strip()
            if not sid:
                continue
            title = (row.get("title") or "").strip()
            url = (row.get("url") or "").strip()
            fpath = (row.get("path") or "").strip()
            retrieved = (row.get("retrieved_utc") or "").strip()

            sha = ""
            if fpath:
                p = Path(fpath)
                if not p.is_absolute():
                    p = (path.parent / p).resolve()
                if p.exists() and p.is_file():
                    sha = _sha256_file(p)
                    if not url:
                        url = f"local:{p.as_posix()}"

            src: Dict[str, Any] = {"id": sid}
            if title:
                src["title"] = title
            if url:
                src["url"] = url
            if sha:
                src["sha256"] = sha
            if retrieved:
                src["retrieved_utc"] = retrieved
            sources.append(src)
    return sources


def build_artifact(
    *,
    
    artifact_id: str,
    domain: str,
    question: str,
    answer_md: str,
    claims: List[Dict[str, Any]],
    sources: List[Dict[str, Any]],
    evidence_links: List[str],
    evidence_artifacts: List[str],
    owner: str,
    cadence: str,
    reporting_primary: str,
    reporting_escalation: str,
    exception_acceptor: str,
    perturbations=perturbations
    perturbations: List[Dict[if perturbations:
    artifact["perturbations"] = perturbations
    
]]
) -> Dict[str, Any]:
    now = _utc_now()
    # keep it simple: 90 days cadence, 1 year exception expiry
    last_review = now
    next_review = now + timedelta(days=90)
    issued = now
    expires = now + timedelta(days=365)

    sections = parse_markdown_sections(answer_md)

    # Ensure required governance fields exist (schema expects them)
    artifact: Dict[str, Any] = {
        "id": artifact_id,
        "domain": domain,
        "question": question,
        "answer": answer_md.strip(),
        "sections": sections,
        "claims": claims,
        "sources": sources,
        "evidence": {"links": evidence_links, "artifacts": evidence_artifacts},
        "review_cycle": {
            "cadence": cadence,
            "owner": owner,
            "last_review_utc": _iso_z(last_review),
            "next_review_utc": _iso_z(next_review),
        },
        "exceptions": {
            "process": "Document exception, assign acceptor, set expiry, review on cadence.",
            "items": [
                {
                    "id": "EX-1",
                    "description": "Coherence metrics are proxies; not a truth guarantee.",
                    "risk_acceptor": exception_acceptor,
                    "issued_utc": _iso_z(issued),
                    "expires_utc": _iso_z(expires),
                }
            ],
        },
        "reporting_channel": {"primary": reporting_primary, "escalation": reporting_escalation},
    }

    return {"coherence_artifact": artifact}


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate a coherence_artifact JSON for UCC coherence_audit.")
    ap.add_argument("--out", required=True, help="Output JSON path (e.g., ucc/tasks/my_artifact.json)")
    ap.add_argument("--id", default="artifact-001", help="Artifact id")
    ap.add_argument("--domain", default="research", help="Domain label (research/governance/etc)")
    ap.add_argument("--question", required=True, help="Question/prompt being answered")
    ap.add_argument("--answer_md", required=True, help="Path to markdown file containing the answer/writeup")
    ap.add_argument("--claims_csv", default="", help="Optional claims CSV (claim_id, claim_text, citations)")
    ap.add_argument("--sources_csv", default="", help="Optional sources CSV (id, title, url, path, retrieved_utc)")
    ap.add_argument("--evidence_link", action="append", default=[], help="Evidence link (repeatable)")
    ap.add_argument("--evidence_artifact", action="append", default=[], help="Evidence artifact label (repeatable)")
    ap.add_argument("--owner", default="maintainers", help="Review owner")
    ap.add_argument("--cadence", default="quarterly", help="Review cadence label")
    ap.add_argument("--reporting_primary", default="github issues", help="Reporting channel (primary)")
    ap.add_argument("--reporting_escalation", default="maintainers", help="Escalation channel")
    ap.add_argument("--exception_acceptor", default="maintainers", help="Exception risk acceptor")
    ap.add_argument("--perturbations_json", default="", help="Optional JSON file containing perturbations list.")

    args = ap.parse_args()

    perturbations: List[Dict[str, Any]] = []
if args.perturbations_json:
    perturbations = load_perturbations_json(Path(args.perturbations_json))


    out_path = Path(args.out)
    ans_path = Path(args.answer_md)
    if not ans_path.exists():
        raise SystemExit(f"answer_md file not found: {ans_path}")

    answer_md = ans_path.read_text(encoding="utf-8")

    claims: List[Dict[str, Any]] = []
    if args.claims_csv:
        claims = load_claims_csv(Path(args.claims_csv))

    sources: List[Dict[str, Any]] = []
    if args.sources_csv:
        sources = load_sources_csv(Path(args.sources_csv))

    # If user didn’t supply claims, scaffold 1 claim so schema passes.
    if not claims:
        # best-effort: cite first source if available
        cits = [sources[0]["id"]] if sources else []
        claims = [{"id": "c1", "text": "See answer body (scaffold claim; replace with precise claims).", "citations": cits}]

    # Evidence links: include explicit links + any http(s) sources
    links = list(args.evidence_link)
    for s in sources:
        url = str(s.get("url", ""))
        if url.startswith("http://") or url.startswith("https://"):
            links.append(url)
    if not links:
        links = ["https://github.com/pdxvoiceteacher/CoherenceLattice"]

    artifact = build_artifact(
        artifact_id=args.id,
        domain=args.domain,
        question=args.question,
        answer_md=answer_md,
        claims=claims,
        sources=sources,
        evidence_links=links,
        evidence_artifacts=list(args.evidence_artifact),
        owner=args.owner,
        cadence=args.cadence,
        reporting_primary=args.reporting_primary,
        reporting_escalation=args.reporting_escalation,
        exception_acceptor=args.exception_acceptor,
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(artifact, indent=2, sort_keys=True), encoding="utf-8")
    print(f"Wrote: {out_path.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
