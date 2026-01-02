from __future__ import annotations

import numpy as np

from konomi.evgpu.ops import matmul, add, mul, reduce_sum, reduce_mean, relu, gelu, layernorm


def test_matmul_matches_numpy():
    rng = np.random.default_rng(0)
    a = rng.standard_normal((16, 16), dtype=np.float32)
    b = rng.standard_normal((16, 16), dtype=np.float32)
    y1 = matmul(a, b)
    y2 = a @ b
    np.testing.assert_allclose(y1, y2, rtol=1e-5, atol=1e-5)


def test_layernorm_mean_var():
    rng = np.random.default_rng(0)
    x = rng.standard_normal((8, 32), dtype=np.float32)
    y = layernorm(x)
    m = np.mean(y, axis=-1)
    v = np.var(y, axis=-1)
    np.testing.assert_allclose(m, np.zeros_like(m), atol=1e-3)
    np.testing.assert_allclose(v, np.ones_like(v), atol=1e-2)


def test_relu_gelu_shapes():
    x = np.array([-2.0, -1.0, 0.0, 1.0, 2.0], dtype=np.float32)
    assert relu(x).shape == x.shape
    assert gelu(x).shape == x.shape


def test_reductions():
    x = np.arange(12, dtype=np.float32).reshape(3, 4)
    assert reduce_sum(x).item() == np.sum(x).item()
    np.testing.assert_allclose(reduce_mean(x, axis=1), np.mean(x, axis=1))