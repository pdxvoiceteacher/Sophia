import importlib


def test_sophia_api_server_import_smoke():
    mod = importlib.import_module("sophia.api.server")
    assert hasattr(mod, "app")
