# Triadic Brain Kernel v16

## Knowledge Field Renormalization

## 1. Purpose

Discovery operates across scales:

`node → corridor → river → terrace → paradigm`

Without scale normalization:

- small discoveries vanish,
- large structures dominate.

Renormalization preserves discovery across scales.

## 2. Knowledge Field

State:

\[
\Psi(x,t)
\]

Define a scale transform:

\[
x \rightarrow \lambda x
\]

Field transforms as:

\[
\Psi'(x) = \lambda^\alpha \Psi(\lambda x)
\]

## 3. Renormalization Operator

Define operator:

\[
R_\lambda[\Psi] = \text{coarse\_grain}(\Psi, \lambda)
\]

## 4. Renormalized PDE

Original discovery equation:

\[
\frac{\partial \Psi}{\partial t} = D\nabla^2\Psi - \nabla \cdot (\Psi\nabla\Phi) + S
\]

Renormalized system:

\[
\frac{\partial \Psi_l}{\partial t} = D_l\nabla^2\Psi_l - \nabla \cdot (\Psi_l\nabla\Phi_l) + S_l
\]

## 5. Scale Flow

Define RG flow:

- \(dD/dl\)
- \(d\Phi/dl\)
- \(dS/dl\)

Stable terraces correspond to fixed points:

- \(\beta(D)=0\)
- \(\beta(\Phi)=0\)

## 6. Terrace Stability Condition

Terrace exists when:

- \(\partial\Psi/\partial t \approx 0\),
- \(\nabla\Psi \approx 0\),

but

- \(\partial^2\Psi/\partial x^2 > 0\) (local minimum of \(\Phi\)).

## 7. Scientific Interpretation

| Regime | RG Interpretation |
|---|---|
| corridor | relevant operator |
| river | scale-stable flow |
| terrace | fixed point |
| orthodoxy | metastable trap |
| rupture | RG bifurcation |

## 8. Renormalization Kernel

CoherenceLattice module:

- `python/src/coherence/kernel/renormalization.py`

```python
import numpy as np


def coarse_grain(field, scale):
    n = len(field) // scale
    return np.mean(field.reshape(n, scale), axis=1)


def renormalize(field, scale):
    coarse = coarse_grain(field, scale)
    return coarse / np.max(coarse)
```

## 9. Result

With Kernel v16:

- small discoveries survive scaling,
- corridors merge into rivers,
- rivers stabilize terraces.

The architecture now behaves like a knowledge renormalization group.
