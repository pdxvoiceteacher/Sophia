from sophia.lens.coherence_lens import evaluate_signal_quality


def test_evaluate_signal_quality_handles_none_and_non_string_fields() -> None:
    records = [
        {"title": None, "abstract": "Alpha beta"},
        {"title": 123, "abstract": None},
        {"title": "Gamma", "abstract": ["delta", "epsilon"]},
    ]

    result = evaluate_signal_quality(records)

    assert set(result.keys()) == {"signal_quality", "noise_ratio"}
    assert 0.0 <= result["signal_quality"] <= 1.0
    assert 0.0 <= result["noise_ratio"] <= 1.0
