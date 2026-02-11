from __future__ import annotations

import subprocess
import sys
from pathlib import Path


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

    result = subprocess.run(
        [
            sys.executable,
            "tools/sophia/frontmatter_lock.py",
            "--docs-dir",
            str(docs_dir),
            "--out",
            str(tmp_path / "report.json"),
        ],
        capture_output=True,
        text=True,
    )
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

    result = subprocess.run(
        [
            sys.executable,
            "tools/sophia/frontmatter_lock.py",
            "--docs-dir",
            str(docs_dir),
            "--out",
            str(tmp_path / "report.json"),
            "--mode",
            "warn",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0


def test_frontmatter_lock_off_mode_skips_checks(tmp_path: Path) -> None:
    docs_dir = tmp_path / "frontmatter"
    docs_dir.mkdir(parents=True, exist_ok=True)
    bad = docs_dir / "sample.md"
    bad.write_text("# Abstract\nself-aware thoughts\n", encoding="utf-8")

    result = subprocess.run(
        [
            sys.executable,
            "tools/sophia/frontmatter_lock.py",
            "--docs-dir",
            str(docs_dir),
            "--out",
            str(tmp_path / "report.json"),
            "--mode",
            "off",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0
