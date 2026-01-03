from __future__ import annotations

from fastapi.testclient import TestClient
from konomi.api.app import app


def test_module_registry(monkeypatch):
    monkeypatch.setenv("KONOMI_API_KEY", "regkey")
    with TestClient(app) as c:
        r = c.get("/v0/modules", headers={"X-API-Key":"regkey"})
        assert r.status_code == 200
        j = r.json()
        assert "schema_version" in j
        assert "app_version" in j
        assert "modules" in j and isinstance(j["modules"], list)
        ids = {m["id"] for m in j["modules"]}
        assert "konomi.femto" in ids
        assert "konomi.cube" in ids
        assert "request_id" in j and len(j["request_id"]) > 0