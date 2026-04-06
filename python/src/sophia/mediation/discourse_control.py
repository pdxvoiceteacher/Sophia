# PURPOSE: detect repetitive reasoning and suggest redirection


def detect_repetition(track_histories, epsilon=1e-4):
    """
    Detect when multiple tracks are repeating similar reasoning.
    """
    if len(track_histories) < 2:
        return False

    latest_values = [t[-1] for t in track_histories if t]

    return max(latest_values) - min(latest_values) < epsilon


def suggest_novel_direction(signal):
    if signal == "entropy_conflict":
        return "Explore externalized harm pathways not yet considered."

    if signal == "aligned":
        return "Introduce a fundamentally different framing or domain."

    return "Generate a novel perspective outside current reasoning basin."
