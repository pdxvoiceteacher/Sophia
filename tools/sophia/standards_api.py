#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

from fastapi import FastAPI, HTTPException
from fastapi.responses import FileResponse, JSONResponse


REPO_ROOT = Path(__file__).resolve().parents[2]
SCHEMA_ROOT = REPO_ROOT / "schema"
POLICY_ROOT = REPO_ROOT / "governance" / "policies"
REGISTRY_ROOT = REPO_ROOT / "governance" / "identity" / "registry_snapshots"
CHANGELOG_PATH = REPO_ROOT / "docs" / "standards_changelog.json"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def git_commit() -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        return result.stdout.strip()
    except Exception:
        return "unknown"


def schema_index() -> list[dict]:
    entries = []
    for path in sorted(SCHEMA_ROOT.rglob("*.schema.json")):
        rel = path.relative_to(REPO_ROOT).as_posix()
        entries.append(
            {
                "name": path.name,
                "path": rel,
                "sha256": sha256_file(path),
            }
        )
    return entries


def policy_index() -> list[dict]:
    entries = []
    if POLICY_ROOT.exists():
        for path in sorted(POLICY_ROOT.glob("*.json")):
            rel = path.relative_to(REPO_ROOT).as_posix()
            payload = load_json(path)
            entries.append(
                {
                    "policy_id": payload.get("policy_id", path.stem),
                    "path": rel,
                    "sha256": sha256_file(path),
                }
            )
    return entries


def registry_index() -> list[dict]:
    entries = []
    if REGISTRY_ROOT.exists():
        for path in sorted(REGISTRY_ROOT.glob("*.json")):
            rel = path.relative_to(REPO_ROOT).as_posix()
            payload = load_json(path)
            entries.append(
                {
                    "snapshot_id": payload.get("snapshot_id", path.stem),
                    "path": rel,
                    "sha256": sha256_file(path),
                }
            )
    return entries


def manifest() -> dict:
    changelog_hash = sha256_file(CHANGELOG_PATH) if CHANGELOG_PATH.exists() else None
    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "git_commit": git_commit(),
        "schemas": schema_index(),
        "policies": policy_index(),
        "registries": registry_index(),
        "changelog": {
            "path": CHANGELOG_PATH.relative_to(REPO_ROOT).as_posix()
            if CHANGELOG_PATH.exists()
            else None,
            "sha256": changelog_hash,
        },
    }


app = FastAPI(title="Sophia Standards Gateway", version="0.1.0")


@app.get("/.well-known/sophia.json")
def well_known() -> dict:
    return {
        "service": "sophia-standards",
        "version": "v1",
        "manifest_url": "/manifest.json",
        "schemas_url": "/schemas",
        "schema_url_template": "/schemas/{name}",
        "policy_url_template": "/policies/mvss/{policy_id}",
        "registry_url_template": "/registry/{snapshot_id}",
        "changelog_url": "/changelog",
        "viewer_url": "/sophia/viewer",
    }


@app.get("/manifest.json")
def manifest_endpoint() -> dict:
    return manifest()


@app.get("/schemas")
def schemas() -> dict:
    return {"schemas": schema_index()}


@app.get("/schemas/{name}")
def schema_by_name(name: str) -> FileResponse:
    for entry in schema_index():
        if entry["name"] == name:
            return FileResponse(REPO_ROOT / entry["path"])
    raise HTTPException(status_code=404, detail="Schema not found")


@app.get("/policies/mvss/{policy_id}")
def policy_by_id(policy_id: str) -> JSONResponse:
    for entry in policy_index():
        if entry["policy_id"] == policy_id:
            return JSONResponse(load_json(REPO_ROOT / entry["path"]))
    raise HTTPException(status_code=404, detail="Policy not found")


@app.get("/registry/{snapshot_id}")
def registry_by_id(snapshot_id: str) -> JSONResponse:
    for entry in registry_index():
        if entry["snapshot_id"] == snapshot_id:
            return JSONResponse(load_json(REPO_ROOT / entry["path"]))
    raise HTTPException(status_code=404, detail="Registry snapshot not found")


@app.get("/changelog")
def changelog() -> JSONResponse:
    if not CHANGELOG_PATH.exists():
        raise HTTPException(status_code=404, detail="Changelog not found")
    return JSONResponse(load_json(CHANGELOG_PATH))
