from __future__ import annotations

from dataclasses import dataclass

from sophia.audit_conservation import audit_conservation


@dataclass
class Witness:
    law_name: str
    residual: float
    within_tolerance: bool


def test_audit_conservation_flags_violations() -> None:
    witnesses = [
        Witness(law_name="mass", residual=0.0001, within_tolerance=True),
        Witness(law_name="energy", residual=0.12, within_tolerance=False),
    ]

    result = audit_conservation(witnesses)

    assert result["semanticMode"] == "non-executive"
    assert len(result["findings"]) == 1
    finding = result["findings"][0]
    assert finding["type"] == "conservation_violation"
    assert finding["law"] == "energy"
    assert finding["residual"] == 0.12
    assert finding["severity"] == "warn"
    assert finding["advisory"] == "watch"


def test_audit_conservation_accepts_dict_witnesses() -> None:
    witnesses = [
        {"law_name": "momentum", "residual": 0.21, "within_tolerance": False},
    ]

    result = audit_conservation(witnesses)

    assert len(result["findings"]) == 1
    assert result["findings"][0]["message"] == "momentum drift exceeds tolerance."
