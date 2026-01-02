from __future__ import annotations

import asyncio
import pytest

from konomi.cube.runtime import CubeRuntime, route_index


def test_route_index_deterministic():
    r1 = route_index("alpha", 9)
    r2 = route_index("alpha", 9)
    r3 = route_index("alpha", 9)
    assert r1 == r2 == r3
    assert 0 <= r1 < 9


def test_backpressure_blocks_second_inflight():
    async def go():
        cube = CubeRuntime(n_nodes=1, queue_max=10, max_inflight=1, process_delay_s=0.05)
        await cube.start()
        t1 = asyncio.create_task(cube.send("k", "first"))
        # allow first to acquire inflight
        await asyncio.sleep(0)

        with pytest.raises(asyncio.TimeoutError):
            await asyncio.wait_for(cube.send("k", "second"), timeout=0.01)

        await t1
        out2 = await asyncio.wait_for(cube.send("k", "second"), timeout=1.0)
        await cube.stop()
        assert "second" in out2

    asyncio.run(go())


def test_fifo_order_single_node():
    async def go():
        cube = CubeRuntime(n_nodes=1, queue_max=100, max_inflight=10, process_delay_s=0.0)
        await cube.start()

        results = []
        for i in range(5):
            results.append(await cube.send("samekey", f"m{i}"))

        await cube.stop()
        assert results[0].endswith("m0")
        assert results[1].endswith("m1")
        assert results[2].endswith("m2")
        assert results[3].endswith("m3")
        assert results[4].endswith("m4")

    asyncio.run(go())