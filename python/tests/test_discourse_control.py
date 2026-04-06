from sophia.mediation.discourse_control import detect_repetition, suggest_novel_direction


def test_detect_repetition_false_when_not_enough_tracks() -> None:
    assert detect_repetition([[0.1]]) is False


def test_detect_repetition_true_for_nearly_identical_latest_values() -> None:
    track_histories = [[0.1, 0.20001], [0.4, 0.20002], [0.9, 0.20000]]
    assert detect_repetition(track_histories, epsilon=1e-3) is True


def test_detect_repetition_false_for_divergent_latest_values() -> None:
    track_histories = [[0.1, 0.2], [0.4, 0.21], [0.9, 0.6]]
    assert detect_repetition(track_histories, epsilon=1e-3) is False


def test_suggest_novel_direction_entropy_conflict() -> None:
    assert (
        suggest_novel_direction("entropy_conflict")
        == "Explore externalized harm pathways not yet considered."
    )


def test_suggest_novel_direction_aligned() -> None:
    assert (
        suggest_novel_direction("aligned")
        == "Introduce a fundamentally different framing or domain."
    )


def test_suggest_novel_direction_default() -> None:
    assert (
        suggest_novel_direction("other")
        == "Generate a novel perspective outside current reasoning basin."
    )
