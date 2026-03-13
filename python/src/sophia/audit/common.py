from __future__ import annotations

from typing import Any


def advisory_docket(finding: str, message: str, *, target: Any | None = None) -> dict[str, Any]:
    rec: dict[str, Any] = {
        "finding": finding,
        "severity": "warn",
        "advisory": "docket",
        "semanticMode": "non-executive",
    }
    if target is not None:
        rec["target"] = str(target)
    return rec


def advisory_watch(finding: str, message: str, *, target: Any | None = None) -> dict[str, Any]:
    rec: dict[str, Any] = {
        "finding": finding,
        "severity": "info",
        "advisory": "watch",
        "semanticMode": "non-executive",
    }
    if target is not None:
        rec["target"] = str(target)
    return rec
