from sophia.audit_audio_coherence import audit_audio_coherence


def test_audio_coherence_low():
    findings = audit_audio_coherence({"phi_total": 0.1})

    assert findings[0]["law"] == "audio_coherence_low"
