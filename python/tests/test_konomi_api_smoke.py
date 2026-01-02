from __future__ import annotations

import os

import pytest
from fastapi.testclient import TestClient

from konomi.api.app import app


def test_health():
    c = TestClient(app)
    r = c.get("/health")
    assert r.status_code == 200
    assert r.json()["ok"] is True


def test_process_requires_api_key():
    c = TestClient(app)
    r = c.post("/v0/process", json={"text": "hi"})
    assert r.status_code == 401


def test_process_ok_with_api_key(monkeypatch):
    monkeypatch.setenv("KONOMI_API_KEY", "devkey")
    c = TestClient(app)
    r = c.post("/v0/process", json={"text": "hi"}, headers={"X-API-Key": "devkey"})
    assert r.status_code == 200
    assert "FemtoModel-stub" in r.json()["output"]


def test_rate_limit_triggers(monkeypatch):
    # Make rate limiter very tight by hammering quickly; should eventually 429
    monkeypatch.setenv("KONOMI_API_KEY", "devkey")
    c = TestClient(app)
    hits = 0
    got_429 = False
    for _ in range(200):
        r = c.post("/v0/process", json={"text": "spam"}, headers={"X-API-Key": "devkey"})
        if r.status_code == 429:
            got_429 = True
            break
        if r.status_code == 200:
            hits += 1
    assert hits > 0
    assert got_429 is True