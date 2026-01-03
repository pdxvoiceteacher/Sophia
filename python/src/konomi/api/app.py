from __future__ import annotations

import os
from contextlib import asynccontextmanager
from typing import Any, Dict, Optional

from fastapi import Depends, FastAPI, Request, WebSocket, WebSocketDisconnect
from pydantic import BaseModel

from konomi.femto.model import FemtoModel
from konomi.api.security import require_api_key, enforce_rate_limit
from konomi.api.audit import AuditLogger, make_audit_middleware, get_app_version
from konomi.cube.runtime import CubeRuntime, route_index
from konomi.registry import get_registry


_model = FemtoModel(dim=16, seed=0)
_audit = AuditLogger()


@asynccontextmanager
async def lifespan(app: FastAPI):
    # startup
    app.state.cube = CubeRuntime(n_nodes=9, queue_max=1024, max_inflight=1024, process_delay_s=0.0)
    await app.state.cube.start()
    yield
    # shutdown
    await app.state.cube.stop()


app = FastAPI(title="KONOMI v0 API (Toy)", version=get_app_version(), lifespan=lifespan)
app.middleware("http")(make_audit_middleware(_audit))


def req_id(req: Request) -> str:
    return str(getattr(req.state, "request_id", ""))


class ProcessIn(BaseModel):
    text: str


class ProcessOut(BaseModel):
    request_id: str
    output: str


class EmbedOut(BaseModel):
    request_id: str
    embedding: list[float]


class CubeSendIn(BaseModel):
    key: str
    text: str


class CubeSendOut(BaseModel):
    request_id: str
    node: int
    output: str


@app.get("/health")
def health(req: Request) -> Dict[str, Any]:
    return {"ok": True, "version": get_app_version(), "request_id": req_id(req)}


@app.get("/v0/modules")
def modules(req: Request, api_key: str = Depends(require_api_key)) -> Dict[str, Any]:
    enforce_rate_limit(req, api_key)
    out = get_registry(get_app_version())
    out["request_id"] = req_id(req)
    return out


@app.post("/v0/process", response_model=ProcessOut)
async def process_endpoint(req: Request, payload: ProcessIn, api_key: str = Depends(require_api_key)) -> ProcessOut:
    enforce_rate_limit(req, api_key)
    out = await _model.process(payload.text)
    return ProcessOut(request_id=req_id(req), output=out)


@app.post("/v0/embed", response_model=EmbedOut)
async def embed_endpoint(req: Request, payload: ProcessIn, api_key: str = Depends(require_api_key)) -> EmbedOut:
    enforce_rate_limit(req, api_key)
    v = await _model.embed(payload.text)
    return EmbedOut(request_id=req_id(req), embedding=v)


@app.post("/v0/cube/send", response_model=CubeSendOut)
async def cube_send(req: Request, payload: CubeSendIn, api_key: str = Depends(require_api_key)) -> CubeSendOut:
    enforce_rate_limit(req, api_key)
    cube: CubeRuntime = req.app.state.cube
    node = route_index(payload.key, cube.n_nodes)
    out = await cube.send(payload.key, payload.text)
    return CubeSendOut(request_id=req_id(req), node=node, output=str(out))


@app.websocket("/ws/process")
async def ws_process(ws: WebSocket):
    await ws.accept()
    api_key = ws.query_params.get("api_key", "")
    expected = os.getenv("KONOMI_API_KEY", "devkey")
    if api_key != expected:
        await ws.send_json({"error": "invalid api_key"})
        await ws.close(code=4401)
        return

    try:
        while True:
            msg = await ws.receive_json()
            text = str(msg.get("text", ""))
            out = await _model.process(text)
            await ws.send_json({"output": out})
    except WebSocketDisconnect:
        return