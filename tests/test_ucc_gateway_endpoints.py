from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_ucc_gateway_endpoints_declared() -> None:
    source = (ROOT / "tools" / "sophia" / "standards_api.py").read_text(encoding="utf-8")
    for route in ["/ucc/index", "/ucc/policies", "/ucc/schemas"]:
        assert route in source, f"Missing UCC endpoint route: {route}"
