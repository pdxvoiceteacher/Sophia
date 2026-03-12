from __future__ import annotations

import json
from pathlib import Path

from sophia.audit_navigation_state import audit_navigation, audit_navigation_state


def test_audit_navigation_pass() -> None:
    payload = audit_navigation({"Psi": 0.9, "deltaStrength": 0.2, "lambdaCritical": 0.1})
    assert payload["decision"] == "pass"
    assert payload["findings"] == []
    assert payload["semanticMode"] == "non-executive"


def test_audit_navigation_warn_and_write(tmp_path: Path) -> None:
    (tmp_path / "bridge").mkdir()
    (tmp_path / "bridge" / "navigation_state.json").write_text(
        json.dumps({"Psi": 0.2, "deltaStrength": 0.7, "lambdaCritical": 0.8}),
        encoding="utf-8",
    )
    result = audit_navigation_state(str(tmp_path))
    written = json.loads((tmp_path / "bridge" / "navigation_audit.json").read_text(encoding="utf-8"))
    assert result["decision"] == "warn"
    assert written["decision"] == "warn"
    ids = {f["id"] for f in result["findings"]}
    assert {"coherence.psiLow", "coherence.deltaHigh", "coherence.lambdaHigh"}.issubset(ids)


def test_audit_navigation_missing_input_fail_closed(tmp_path: Path) -> None:
    result = audit_navigation_state(str(tmp_path))
    assert result["decision"] == "fail"
    assert result["findings"][0]["id"] == "navigation.missing"
    assert result["findings"][0]["advisory"] == "docket"
