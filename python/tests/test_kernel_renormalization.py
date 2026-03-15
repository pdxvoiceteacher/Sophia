from __future__ import annotations

import numpy as np
import pytest

from coherence.kernel.renormalization import coarse_grain, renormalize


def test_coarse_grain_means_fixed_blocks() -> None:
    field = np.array([1.0, 3.0, 2.0, 6.0])
    coarse = coarse_grain(field, scale=2)

    assert np.allclose(coarse, np.array([2.0, 4.0]))


def test_coarse_grain_trims_remainder() -> None:
    field = np.array([2.0, 4.0, 8.0, 10.0, 999.0])
    coarse = coarse_grain(field, scale=2)

    assert np.allclose(coarse, np.array([3.0, 9.0]))


def test_renormalize_scales_to_unit_peak_magnitude() -> None:
    field = np.array([-2.0, -6.0, 4.0, 8.0])
    normalized = renormalize(field, scale=2)

    assert np.allclose(normalized, np.array([-2.0 / 3.0, 1.0]))


@pytest.mark.parametrize(
    ("field", "scale", "message"),
    [
        ([], 2, "field must be non-empty"),
        ([1.0, 2.0], 0, "scale must be positive"),
        ([1.0, 2.0], 3, "scale cannot exceed field length"),
    ],
)
def test_renormalization_validation(field: list[float], scale: int, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        coarse_grain(field, scale)
