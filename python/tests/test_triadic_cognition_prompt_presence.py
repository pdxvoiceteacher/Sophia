from pathlib import Path


def test_triadic_cognition_prompt_exists():
    path = Path("python/src/sophia/prompts/triadic_cognition_conditioning_v1.md")
    assert path.exists(), f"Missing prompt file: {path}"


def test_triadic_cognition_prompt_has_core_terms():
    path = Path("python/src/sophia/prompts/triadic_cognition_conditioning_v1.md")
    text = path.read_text(encoding="utf-8")
    for term in ["Ψ = E × T", "generative", "extractive", "counter-perturbation"]:
        assert term in text, f"Missing core term: {term}"
