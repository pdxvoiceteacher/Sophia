from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_web_viewer_required_ids():
    html = read_text(ROOT / "web" / "index.html")
    required_ids = [
        "run-picker",
        "governance-overview",
        "election-summary",
        "decision-proof",
        "ledger-anchor",
        "warrant",
        "execution-receipt",
        "execution-diffs",
        "epoch-comparison",
        "epoch-findings",
        "epoch-findings-link",
        "json-viewer",
    ]
    for element_id in required_ids:
        assert f'id="{element_id}"' in html, f"Missing element id: {element_id}"


def test_web_viewer_governance_files_referenced():
    app_js = read_text(ROOT / "web" / "src" / "app.js")
    for filename in [
        "policy_resolution.json",
        "election.json",
        "tally.json",
        "decision.json",
        "warrant.json",
        "epoch.json",
        "epoch_metrics.json",
        "epoch_findings.json",
    ]:
        assert filename in app_js, f"Missing reference to {filename} in app.js"
