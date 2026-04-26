import importlib


def test_sophia_api_package_import_smoke():
    mod = importlib.import_module("sophia.api")
    assert hasattr(mod, "emit_attention_updates")
