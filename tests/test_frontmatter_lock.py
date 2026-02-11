from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def run_lock(docs_dir: Path, out_path: Path, *extra: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            "tools/sophia/frontmatter_lock.py",
            "--docs-dir",
            str(docs_dir),
            "--out",
            str(out_path),
            *extra,
        ],
        capture_output=True,
        text=True,
    )


def test_frontmatter_lock_catches_banned_terms(tmp_path: Path) -> None:
    docs_dir = tmp_path / "frontmatter"
    docs_dir.mkdir(parents=True, exist_ok=True)
    bad = docs_dir / "sample.md"
    bad.write_text(
        "# Abstract\nBehavioral test signals only; does not imply consciousness.\nTEL is provenance-only.\n"
        "Metrics are diagnostic and governance-facing, not claims of sentience or agency.\n"
        "This methods section describes lived experience and volition.\n",
        encoding="utf-8",
    )

    result = run_lock(docs_dir, tmp_path / "report.json")
    assert result.returncode != 0


def test_frontmatter_lock_passes_approved_file() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "tools/sophia/frontmatter_lock.py",
            "--docs-dir",
            "docs/frontmatter",
            "--out",
            "frontmatter_lock_report.json",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0


def test_frontmatter_lock_warn_mode_does_not_fail(tmp_path: Path) -> None:
    docs_dir = tmp_path / "frontmatter"
    docs_dir.mkdir(parents=True, exist_ok=True)
    bad = docs_dir / "sample.md"
    bad.write_text("# Abstract\nThis includes lived experience.\n", encoding="utf-8")

    result = run_lock(docs_dir, tmp_path / "report.json", "--mode", "warn")
    assert result.returncode == 0


def test_frontmatter_lock_off_mode_skips_checks(tmp_path: Path) -> None:
    docs_dir = tmp_path / "frontmatter"
    docs_dir.mkdir(parents=True, exist_ok=True)
    bad = docs_dir / "sample.md"
    bad.write_text("# Abstract\nself-aware thoughts\n", encoding="utf-8")

    out_path = tmp_path / "report.json"
    result = run_lock(docs_dir, out_path, "--mode", "off")
    assert result.returncode == 0
    report = json.loads(out_path.read_text(encoding="utf-8"))
    assert report["decision"] == "skipped"


def test_frontmatter_lock_profiles_change_severity_and_governance_hint(tmp_path: Path) -> None:
    docs_dir = tmp_path / "frontmatter"
    docs_dir.mkdir(parents=True, exist_ok=True)
    bad = docs_dir / "sample.md"
    bad.write_text(
        "# Abstract\nBehavioral test signals only; does not imply consciousness.\nTEL is provenance-only.\n"
        "Metrics are diagnostic and governance-facing, not claims of sentience or agency.\n"
        "The model has thoughts.\n",
        encoding="utf-8",
    )

    publication_report = tmp_path / "publication_report.json"
    publication = run_lock(docs_dir, publication_report, "--profile", "publication")
    assert publication.returncode != 0

    safeguard_report = tmp_path / "safeguard_report.json"
    safeguard = run_lock(docs_dir, safeguard_report, "--profile", "safeguard")
    assert safeguard.returncode == 0
    payload = json.loads(safeguard_report.read_text(encoding="utf-8"))
    assert payload["governance_hints"]["due_process_required"] is True
    assert payload["governance_hints"]["sentinel_state_hint"] == "protect"
