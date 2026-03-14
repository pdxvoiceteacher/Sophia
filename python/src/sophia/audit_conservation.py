from __future__ import annotations

from dataclasses import asdict, is_dataclass
from typing import Any


def _witness_to_mapping(witness: Any) -> dict[str, Any]:
    if is_dataclass(witness):
        return asdict(witness)
    if isinstance(witness, dict):
        return witness
    return {
        "law_name": getattr(witness, "law_name", "unknown_law"),
        "residual": getattr(witness, "residual", None),
        "within_tolerance": getattr(witness, "within_tolerance", True),
    }


def audit_conservation(witnesses: list[Any]) -> dict[str, Any]:
    findings: list[dict[str, Any]] = []

    for witness in witnesses:
        data = _witness_to_mapping(witness)
        if not bool(data.get("within_tolerance", True)):
            law_name = str(data.get("law_name", "unknown_law"))
            residual = data.get("residual")
            findings.append(
                {
                    "type": "conservation_violation",
                    "law": law_name,
                    "residual": residual,
                    "severity": "warn",
                    "advisory": "watch",
                    "message": f"{law_name} drift exceeds tolerance.",
                }
            )

    return {
        "semanticMode": "non-executive",
        "findings": findings,
    }
