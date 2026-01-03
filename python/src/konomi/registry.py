from __future__ import annotations

from typing import Any, Dict, List


REGISTRY_SCHEMA_VERSION = "0.1"


def get_registry(app_version: str) -> Dict[str, Any]:
    """
    Basic module registry for KONOMI v0.
    This is descriptive metadata (not a compliance claim).
    """
    modules: List[Dict[str, Any]] = [
        {
            "id": "konomi.evgpu",
            "version": "0.1.0",
            "status": "baseline",
            "description": "CPU tensor ops (NumPy/BLAS): matmul/add/mul/reduce/activations/layernorm.",
            "endpoints": [],
        },
        {
            "id": "konomi.femto",
            "version": "0.1.0",
            "status": "stub",
            "description": "Async FemtoModel wiring stub (process/embed), deterministic for benchmarking.",
            "endpoints": ["/v0/process", "/v0/embed"],
        },
        {
            "id": "konomi.blockarray",
            "version": "0.1.0",
            "status": "baseline",
            "description": "Sparse chunked 3D BlockArray (allocate-on-write, bounded scan).",
            "endpoints": [],
        },
        {
            "id": "konomi.cube",
            "version": "0.1.0",
            "status": "baseline",
            "description": "9-node async router runtime (deterministic routing, backpressure).",
            "endpoints": ["/v0/cube/send"],
        },
        {
            "id": "konomi.api",
            "version": app_version,
            "status": "demo",
            "description": "FastAPI REST+WS, API key auth, rate limiting, audit logging (JSONL).",
            "endpoints": ["/health", "/v0/modules", "/ws/process"],
        },
    ]

    return {
        "schema_version": REGISTRY_SCHEMA_VERSION,
        "app_version": app_version,
        "modules": modules,
        "notes": "Registry is descriptive metadata for reviewers; not a compliance certification.",
    }