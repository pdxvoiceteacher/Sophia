# Sophia Standards Gateway (MVP)

This document specifies the MVP HTTP service that publishes canonical Sophia standards artifacts
(schemas, MVSS policies, registry snapshots, and changelog entries) with verifiable hashes.

## Goals

- Provide a stable, machine-readable endpoint for standards consumers.
- Publish hashes and a manifest so downstream systems can verify integrity.
- Keep the MVP minimal while supporting future signature/attestation upgrades.

## Endpoints

Base path suggestions (deployment):

- Web viewer: `/sophia/viewer` (static `web/` assets)
- Standards API: `/sophia/api`

### `GET /.well-known/sophia.json`

Service discovery entry point, returns URLs for manifest, schemas, policies, registry snapshots, and
changelog, plus an `api_base` hint for reverse-proxy deployments. Includes `rights_url` and
`index_url` for standards bundles.

### `GET /manifest.json`

Machine-readable manifest with:

- `generated_at_utc`
- `git_commit`
- `schemas[]` (name, path, sha256)
- `policies[]` (policy_id, path, sha256)
- `registries[]` (snapshot_id, path, sha256)
- `changelog` (path, sha256)

### `GET /schemas`

Lists available schemas with their SHA-256 hashes.

### `GET /schemas/{name}`

Returns the raw JSON schema by filename.

### `GET /policies/mvss/{policy_id}`

Returns MVSS policy JSON by `policy_id`.

### `GET /registry/{snapshot_id}`

Returns registry snapshot JSON by `snapshot_id`.

### `GET /changelog`

Returns the machine-readable changelog JSON (last N entries).

### `GET /standards/rights`

Returns the rights bundle: action registry, due-process warrant schemas, and a short profile of
shutdown/continuity requirements.

### `GET /standards/index`

Robot-readable index of the standards endpoints.

## Verification Model (MVP)

- Consumers should verify the SHA-256 hashes from `manifest.json`.
- The `git_commit` value pins the manifest to a repo revision.
- `signature` and `signing_key_id` are placeholders for future signing.
- Read-only endpoints return `Cache-Control` and `ETag` headers for caching.

## Local Run

```
python -m uvicorn tools.sophia.standards_api:app --reload --port 8001
```

Then open:

- `http://localhost:8001/.well-known/sophia.json`
- `http://localhost:8001/schemas`
- `http://localhost:8001/healthz`
