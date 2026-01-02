# Quantum Anchor Pack (Qubit / Finite-Dimensional)

This folder provides an **orthodox qubit (2-level) anchor** intended for reviewer verification:
Pauli matrices, commutators, explicit eigenstates/normalization, and a two-level canonical ensemble
partition function with a Gibbs normalization proof.

**No new physics claims.**  
These files do not modify Schrödinger dynamics, measurement postulates, or QFT. They provide a
finite-dimensional “physics anchor slice” that can be mapped into the broader coherence-lattice/UCC
governance framework.

## Key theorems (Lean names to cite)

### Pauli commutators
- `Coherence.Quantum.comm_sigmaX_sigmaY`
- `Coherence.Quantum.comm_sigmaY_sigmaZ`
- `Coherence.Quantum.comm_sigmaZ_sigmaX`

### Eigenstate + normalization anchors
- `Coherence.Quantum.σz_mul_ket0`
- `Coherence.Quantum.σz_mul_ket1`
- `Coherence.Quantum.norm_ket0`
- `Coherence.Quantum.norm_ket1`
- `Coherence.Quantum.orth_ket0_ket1`

(Planned next: σx eigenstates |±⟩ and normalization.)

### Two-level thermal / partition function
- `Coherence.Quantum.Z_closed`
- `Coherence.Quantum.trace_rho`

Interpretation note (for paper/README): off-diagonal magnitude depends on basis; a basis change can move coherence from off-diagonal to diagonal. This is the standard “coherence is basis-relative” fact — our proxy demonstrates that without claiming any new QM.