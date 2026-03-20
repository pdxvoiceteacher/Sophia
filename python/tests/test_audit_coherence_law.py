from __future__ import annotations

from sophia.audit_coherence_law import audit_coherence_law


def test_fragmentation_noise_finding() -> None:
    findings = audit_coherence_law({"score": 0.2, "deltaS": 0.8})

    assert len(findings) == 1
    assert findings[0]["law"] == "fragmentation_noise"


def test_coherence_growth_finding() -> None:
    findings = audit_coherence_law({"score": 0.8, "deltaS": 0.2})

    assert len(findings) == 1
    assert findings[0]["law"] == "coherence_growth"
