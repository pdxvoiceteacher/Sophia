from __future__ import annotations

import os
from typing import Any, Dict

from fastapi import Depends, FastAPI, Request, WebSocket, WebSocketDisconnect
from pydantic import BaseModel

from konomi.femto.model import FemtoModel
from konomi.api.security import require_api_key, enforce_rate_limit


APP_VERSION = os.getenv("KONOMI_VERSION", "0.1.0-dev")

app = FastAPI(title="KONOMI v0 API (Toy)", version=APP_VERSION)

_model = FemtoModel(dim=16, seed=0)


class ProcessIn(BaseModel):
    text: str


class ProcessOut(BaseModel):
    output: str


class EmbedOut(BaseModel):
    embedding: list[float]


@app.get("/health")
def health() -> Dict[str, Any]:
    return {"ok": True, "version": APP_VERSION}


@app.post("/v0/process", response_model=ProcessOut)
async def process_endpoint(
    req: Request,
    payload: ProcessIn,
    api_key: str = Depends(require_api_key),
) -> ProcessOut:
    enforce_rate_limit(req, api_key)
    out = await _model.process(payload.text)
    return ProcessOut(output=out)


@app.post("/v0/embed", response_model=EmbedOut)
async def embed_endpoint(
    req: Request,
    payload: ProcessIn,
    api_key: str = Depends(require_api_key),
) -> EmbedOut:
    enforce_rate_limit(req, api_key)
    v = await _model.embed(payload.text)
    return EmbedOut(embedding=v)


@app.websocket("/ws/process")
async def ws_process(ws: WebSocket):
    # Simple API key gating via query param: ?api_key=...
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