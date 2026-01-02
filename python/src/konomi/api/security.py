from __future__ import annotations

import os
import time
from dataclasses import dataclass
from typing import Dict, Optional

from fastapi import Header, HTTPException, Request


def require_api_key(x_api_key: Optional[str] = Header(default=None)) -> str:
    expected = os.getenv("KONOMI_API_KEY", "devkey")
    if x_api_key is None or x_api_key != expected:
        raise HTTPException(status_code=401, detail="Invalid or missing API key (X-API-Key).")
    return x_api_key


@dataclass
class TokenBucket:
    capacity: float
    refill_per_s: float
    tokens: float
    last_ts: float


class RateLimiter:
    """
    Simple in-memory token bucket per client id (API key or IP).
    Suitable for dev/demo. For production, use redis / gateway.
    """
    def __init__(self, capacity: float = 30.0, refill_per_s: float = 10.0) -> None:
        self.capacity = float(capacity)
        self.refill_per_s = float(refill_per_s)
        self.buckets: Dict[str, TokenBucket] = {}

    def allow(self, client_id: str, cost: float = 1.0) -> bool:
        now = time.time()
        b = self.buckets.get(client_id)
        if b is None:
            b = TokenBucket(self.capacity, self.refill_per_s, self.capacity, now)
            self.buckets[client_id] = b

        # refill
        dt = max(0.0, now - b.last_ts)
        b.tokens = min(b.capacity, b.tokens + dt * b.refill_per_s)
        b.last_ts = now

        if b.tokens >= cost:
            b.tokens -= cost
            return True
        return False


_limiter = RateLimiter(capacity=60.0, refill_per_s=20.0)


def enforce_rate_limit(request: Request, api_key: str) -> None:
    # Prefer API key; fallback to client host.
    cid = api_key or (request.client.host if request.client else "unknown")
    if not _limiter.allow(cid, cost=1.0):
        raise HTTPException(status_code=429, detail="Rate limit exceeded.")