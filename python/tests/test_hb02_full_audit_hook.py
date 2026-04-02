from sophia.hb02_full_audit_hook import audit_full_hb02


def test_audit_full_hb02_returns_pass_without_warning(capsys) -> None:
    packet = {
        "baseline": {
            "literal_output": "baseline literal",
            "allegorical_output": "baseline allegorical",
        },
        "conditioned": {
            "literal_output": "conditioned literal",
            "allegorical_output": "conditioned allegorical",
        },
        "true_coherence": "coherent",
        "coherence_context": "context",
    }

    result = audit_full_hb02(packet)
    captured = capsys.readouterr()

    assert result["audit_pass"] is True
    assert captured.out == ""


def test_audit_full_hb02_prints_warning_on_failure(capsys) -> None:
    packet = {
        "baseline": {"literal_output": "only baseline"},
        "conditioned": {"literal_output": "only conditioned"},
        "true_coherence": "false_coherence",
        "coherence_context": "",
    }

    result = audit_full_hb02(packet)
    captured = capsys.readouterr()

    assert result["audit_pass"] is False
    assert "⚠️ SOPHIA WARNING" in captured.out
    assert "invalid_field_context" in captured.out
