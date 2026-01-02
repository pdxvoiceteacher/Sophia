from __future__ import annotations

import asyncio

from konomi.femto.model import FemtoModel


def test_process_is_deterministic():
    m = FemtoModel(seed=0)
    out1 = asyncio.run(m.process("hello"))
    out2 = asyncio.run(m.process("hello"))
    assert out1 == out2
    assert "FemtoModel-stub" in out1


def test_embed_dim():
    m = FemtoModel(dim=16, seed=0)
    v = asyncio.run(m.embed("hello"))
    assert isinstance(v, list)
    assert len(v) == 16