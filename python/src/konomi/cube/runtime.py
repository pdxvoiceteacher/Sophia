from __future__ import annotations

import asyncio
import hashlib
import time
from dataclasses import dataclass
from typing import Any, Callable, Optional, Dict, List


def route_index(key: str, n_nodes: int) -> int:
    """
    Deterministic routing (stable across runs; NOT Python's built-in hash).
    """
    h = hashlib.blake2b(key.encode("utf-8"), digest_size=8).digest()
    return int.from_bytes(h, "little") % n_nodes


@dataclass
class CubeMessage:
    key: str
    payload: Any
    created_ns: int
    fut: asyncio.Future


class CubeNode:
    def __init__(
        self,
        node_id: int,
        *,
        queue_max: int = 1024,
        max_inflight: int = 1024,
        process_delay_s: float = 0.0,
        handler: Optional[Callable[[CubeMessage], Any]] = None,
    ) -> None:
        self.node_id = node_id
        self.queue: asyncio.Queue = asyncio.Queue(maxsize=queue_max)
        self.inflight = asyncio.Semaphore(max_inflight)
        self.process_delay_s = float(process_delay_s)
        self.handler = handler
        self._task: Optional[asyncio.Task] = None
        self._running = False

    async def start(self) -> None:
        if self._running:
            return
        self._running = True
        self._task = asyncio.create_task(self._worker())

    async def stop(self) -> None:
        if not self._running:
            return
        self._running = False
        # sentinel to stop worker
        await self.queue.put(None)
        if self._task is not None:
            await self._task

    async def _worker(self) -> None:
        while True:
            msg = await self.queue.get()
            if msg is None:
                self.queue.task_done()
                break
            try:
                if self.process_delay_s > 0:
                    await asyncio.sleep(self.process_delay_s)

                if self.handler is None:
                    # Default handler: echo payload with node tag
                    result = f"[CubeNode:{self.node_id}] {msg.payload}"
                else:
                    result = self.handler(msg)

                if not msg.fut.done():
                    msg.fut.set_result(result)
            except Exception as e:
                if not msg.fut.done():
                    msg.fut.set_exception(e)
            finally:
                self.inflight.release()
                self.queue.task_done()


class CubeRuntime:
    """
    Minimal 9-node (configurable) async message router with:
    - deterministic routing by key
    - bounded inflight (backpressure)
    - bounded queue
    - predictable per-node processing order (FIFO)
    """

    def __init__(
        self,
        *,
        n_nodes: int = 9,
        queue_max: int = 1024,
        max_inflight: int = 1024,
        process_delay_s: float = 0.0,
        handler: Optional[Callable[[CubeMessage], Any]] = None,
    ) -> None:
        if n_nodes <= 0:
            raise ValueError("n_nodes must be > 0")
        self.n_nodes = int(n_nodes)
        self.nodes: List[CubeNode] = [
            CubeNode(i, queue_max=queue_max, max_inflight=max_inflight, process_delay_s=process_delay_s, handler=handler)
            for i in range(self.n_nodes)
        ]

    async def start(self) -> None:
        for n in self.nodes:
            await n.start()

    async def stop(self) -> None:
        for n in self.nodes:
            await n.stop()

    async def send(self, key: str, payload: Any) -> Any:
        idx = route_index(key, self.n_nodes)
        node = self.nodes[idx]
        await node.inflight.acquire()  # backpressure gate (blocks)
        loop = asyncio.get_running_loop()
        fut = loop.create_future()
        msg = CubeMessage(key=key, payload=payload, created_ns=time.perf_counter_ns(), fut=fut)
        await node.queue.put(msg)
        return await fut