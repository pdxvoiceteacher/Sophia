from __future__ import annotations

import csv
import json
import subprocess
from dataclasses import asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from .core import Note, Phrase, Sequence, clamp01, safe_mean


def _repo_root() -> Path:
    # python/src/coherence_music/analyze.py -> python/src/coherence_music -> python/src -> python -> repo
    return Path(__file__).resolve().parents[3]


def _git_commit(repo: Path) -> str:
    try:
        out = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=str(repo))
        return out.decode("utf-8", errors="replace").strip()
    except Exception:
        return "UNKNOWN"


def _sha256_file(path: Path) -> str:
    import hashlib
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _metric_series(metrics: Dict[str, List[float]], i: int) -> Dict[str, float]:
    def g(k: str, default: float = 0.0) -> float:
        xs = metrics.get(k, [])
        return float(xs[i]) if i < len(xs) else float(default)

    E = g("E")
    T = g("T")
    PSI = g("PSI", default=E * T)
    return {
        "E": E,
        "T": T,
        "PSI": PSI,
        "DELTA_S": g("DELTA_S"),
        "E_SYM": g("E_SYM"),
        "LAMBDA": g("LAMBDA"),
    }


def build_trace(metrics: Dict[str, List[float]], seq: Sequence) -> Dict[str, Any]:
    """
    Build a step-aligned trace: each phrase corresponds to one timestep.
    (Assumes seq.phrases aligns to metrics length, as produced by the engine.)
    """
    n = min(len(seq.phrases), len(metrics.get("E", [])), len(metrics.get("T", [])))
    steps: List[Dict[str, Any]] = []

    for i in range(n):
        ph = seq.phrases[i]
        ms = _metric_series(metrics, i)

        pitches = [int(n.pitch) for n in ph.notes]
        vels = [int(n.velocity) for n in ph.notes]
        durs = [float(n.duration_beats) for n in ph.notes]

        steps.append(
            {
                "t": i + 1,
                "label": ph.label,
                "category": ph.category,
                "pitches": pitches,
                "velocities": vels,
                "durations_beats": durs,
                **ms,
            }
        )

    return {
        "run_id": seq.name,
        "bpm": int(seq.bpm),
        "steps": steps,
    }


def _counts_by_category(steps: List[Dict[str, Any]]) -> Dict[str, int]:
    out: Dict[str, int] = {}
    for s in steps:
        c = str(s.get("category", ""))
        out[c] = out.get(c, 0) + 1
    return out


def _lift(steps: List[Dict[str, Any]], cat: str, metric_key: str) -> Dict[str, float]:
    """
    Compute 'lift' of metric within steps where category==cat.
    lift = mean(metric | cat) / mean(metric overall)  (safe if denom 0)
    """
    overall = [float(s.get(metric_key, 0.0)) for s in steps]
    sel = [float(s.get(metric_key, 0.0)) for s in steps if str(s.get("category")) == cat]
    m_all = safe_mean(overall)
    m_sel = safe_mean(sel)
    lift = (m_sel / m_all) if m_all > 1e-12 else 0.0
    return {"mean_all": m_all, "mean_cat": m_sel, "lift": lift, "n_cat": len(sel), "n_all": len(overall)}


def audit_trace(trace: Dict[str, Any]) -> Dict[str, Any]:
    steps = list(trace.get("steps", []))
    counts = _counts_by_category(steps)

    # Coverage: how many non-BASE categories appeared at least once
    cats = sorted(set(s.get("category", "") for s in steps))
    non_base = [c for c in cats if c and c != "BASE"]
    non_base_hit = [c for c in non_base if counts.get(c, 0) > 0]
    coverage = (len(non_base_hit) / len(non_base)) if non_base else 0.0

    # “Correlation-ish” evidence: lifts for each metric vs category
    lifts: Dict[str, Dict[str, Dict[str, float]]] = {}
    for cat in sorted(set(counts.keys())):
        lifts[cat] = {
            "E": _lift(steps, cat, "E"),
            "T": _lift(steps, cat, "T"),
            "PSI": _lift(steps, cat, "PSI"),
            "DELTA_S": _lift(steps, cat, "DELTA_S"),
            "E_SYM": _lift(steps, cat, "E_SYM"),
            "LAMBDA": _lift(steps, cat, "LAMBDA"),
        }

    return {
        "run_id": trace.get("run_id", ""),
        "bpm": trace.get("bpm", 120),
        "n_steps": len(steps),
        "categories_present": sorted(counts.keys()),
        "counts_by_category": counts,
        "non_base_coverage": coverage,
        "metric_lifts": lifts,
    }


def write_trace_and_audit(
    outdir: Path,
    metrics: Dict[str, List[float]],
    seq: Sequence,
    midi_path: Optional[Path] = None,
    *,
    evidence_links: Optional[List[str]] = None,
) -> Dict[str, Path]:
    """
    Writes:
      - trace.json / trace.csv
      - audit_summary.json / audit_summary.md
      - ucc_artifact.json (wrapper for UCC check_required_sections)
    Returns dict of paths.
    """
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    repo = _repo_root()
    git_commit = _git_commit(repo)

    trace = build_trace(metrics, seq)
    audit = audit_trace(trace)

    # Write trace JSON
    trace_json = outdir / f"{seq.name}_trace.json"
    trace_json.write_text(json.dumps(trace, indent=2, sort_keys=True), encoding="utf-8")

    # Write trace CSV
    trace_csv = outdir / f"{seq.name}_trace.csv"
    steps = trace["steps"]
    cols = ["t", "label", "category", "E", "T", "PSI", "DELTA_S", "E_SYM", "LAMBDA", "pitches", "velocities", "durations_beats"]
    with trace_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for s in steps:
            row = dict(s)
            row["pitches"] = " ".join(map(str, row.get("pitches", [])))
            row["velocities"] = " ".join(map(str, row.get("velocities", [])))
            row["durations_beats"] = " ".join(map(lambda x: f"{float(x):g}", row.get("durations_beats", [])))
            w.writerow({k: row.get(k, "") for k in cols})

    # audit summary JSON
    audit_json = outdir / f"{seq.name}_audit_summary.json"
    audit_json.write_text(json.dumps(audit, indent=2, sort_keys=True), encoding="utf-8")

    # audit summary MD
    audit_md = outdir / f"{seq.name}_audit_summary.md"
    md_lines = [
        f"# Coherence Music Audit Summary — {seq.name}",
        "",
        f"- git_commit: `{git_commit}`",
        f"- bpm: **{audit.get('bpm')}**",
        f"- steps: **{audit.get('n_steps')}**",
        f"- non-base coverage: **{audit.get('non_base_coverage'):.3f}**",
        "",
        "## Counts by category",
        "",
        "| category | count |",
        "|---|---:|",
    ]
    for k, v in sorted(audit["counts_by_category"].items()):
        md_lines.append(f"| {k} | {v} |")

    md_lines += [
        "",
        "## Metric lift (mean metric within category / overall mean)",
        "",
        "_Lift > 1 means the metric is higher on steps where that category was selected._",
        "",
    ]

    # show compact table for key categories
    key_metrics = ["E", "T", "PSI", "DELTA_S", "E_SYM", "LAMBDA"]
    md_lines += ["| category | " + " | ".join(key_metrics) + " |", "|---|" + "|".join(["---:"] * len(key_metrics)) + "|"]
    for cat in sorted(audit["metric_lifts"].keys()):
        vals = []
        for mk in key_metrics:
            vals.append(f"{audit['metric_lifts'][cat][mk]['lift']:.2f}")
        md_lines.append("| " + cat + " | " + " | ".join(vals) + " |")

    audit_md.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    # UCC wrapper artifact
    artifact = {
        "coherence_music_audit": {
            "git_commit": git_commit,
            "run_id": seq.name,
            "bpm": int(seq.bpm),
            "trace_json": str(trace_json.as_posix()),
            "trace_csv": str(trace_csv.as_posix()),
            "audit_json": str(audit_json.as_posix()),
            "audit_md": str(audit_md.as_posix()),
            "midi_path": str(midi_path.as_posix()) if midi_path else "",
            "evidence_links": evidence_links or [],
            "notes": "Engine selects phrase categories as a function of GUFT-like metrics; see metric_lifts table for alignment evidence.",
        }
    }
    artifact_json = outdir / f"{seq.name}_ucc_artifact.json"
    artifact_json.write_text(json.dumps(artifact, indent=2, sort_keys=True), encoding="utf-8")

    # hashes (optional but helpful)
    if midi_path and midi_path.exists():
        hashes = {
            "midi_sha256": _sha256_file(midi_path),
            "trace_sha256": _sha256_file(trace_json),
            "audit_sha256": _sha256_file(audit_json),
        }
        (outdir / f"{seq.name}_hashes.json").write_text(json.dumps(hashes, indent=2, sort_keys=True), encoding="utf-8")

    return {
        "trace_json": trace_json,
        "trace_csv": trace_csv,
        "audit_json": audit_json,
        "audit_md": audit_md,
        "ucc_artifact_json": artifact_json,
    }