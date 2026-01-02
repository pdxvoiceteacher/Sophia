from __future__ import annotations

import numpy as np


def matmul(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """CPU matmul using NumPy/BLAS."""
    return a @ b


def add(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return a + b


def mul(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return a * b


def reduce_sum(x: np.ndarray, axis=None, keepdims: bool = False) -> np.ndarray:
    return np.sum(x, axis=axis, keepdims=keepdims)


def reduce_mean(x: np.ndarray, axis=None, keepdims: bool = False) -> np.ndarray:
    return np.mean(x, axis=axis, keepdims=keepdims)


def relu(x: np.ndarray) -> np.ndarray:
    return np.maximum(x, 0)


def gelu(x: np.ndarray) -> np.ndarray:
    """
    GELU (tanh approximation), stable and CPU-only.
    0.5*x*(1 + tanh(sqrt(2/pi)*(x + 0.044715*x^3)))
    """
    x = np.asarray(x, dtype=np.float32)
    c = np.sqrt(2.0 / np.pi).astype(np.float32)
    return 0.5 * x * (1.0 + np.tanh(c * (x + 0.044715 * (x ** 3))))


def layernorm(x: np.ndarray, eps: float = 1e-5) -> np.ndarray:
    """
    LayerNorm over last dimension.
    """
    x = np.asarray(x, dtype=np.float32)
    mean = np.mean(x, axis=-1, keepdims=True)
    var = np.mean((x - mean) ** 2, axis=-1, keepdims=True)
    return (x - mean) / np.sqrt(var + eps)