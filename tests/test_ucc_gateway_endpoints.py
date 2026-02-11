from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_ucc_gateway_endpoints_declared() -> None:
    source = (ROOT / "tools" / "sophia" / "standards_api.py").read_text(encoding="utf-8")
    for route in ["/ucc/index", "/ucc/policies", "/ucc/schemas", "/sophia/local-runs/{run_id}/{mode}/{filename}"]:
        assert route in source, f"Missing UCC endpoint route: {route}"
