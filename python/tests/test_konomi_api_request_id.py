from __future__ import annotations

from fastapi.testclient import TestClient
from konomi.api.app import app


def test_request_id_header_and_body(monkeypatch):
    monkeypatch.setenv("KONOMI_API_KEY", "ridkey")
    with TestClient(app) as c:
        r = c.post("/v0/process", json={"text":"hello"}, headers={"X-API-Key":"ridkey"})
        assert r.status_code == 200
        rid_h = r.headers.get("X-Request-ID")
        assert rid_h is not None and len(rid_h) > 0
        j = r.json()
        assert j["request_id"] == rid_h