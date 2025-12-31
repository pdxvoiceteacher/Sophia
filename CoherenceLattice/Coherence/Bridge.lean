import CoherenceLattice.Coherence.Basic
import CoherenceLattice.Coherence.Lattice

namespace Coherence

set_option linter.style.commandStart false

/-- Package a Basic.CoherenceInput into the lattice State (unit square). -/
def CoherenceInput.toState (x : CoherenceInput) : Lattice.State :=
  (⟨x.E, ⟨x.hE0, x.hE1⟩⟩, ⟨x.T, ⟨x.hT0, x.hT1⟩⟩)

/-- The two Ψ definitions agree after coercing into the lattice State. -/
lemma psi_eq_lattice_psi (x : CoherenceInput) :
    Coherence.psi x = Lattice.psi (x.toState) := by
  simp [Coherence.psi, Lattice.psi, Lattice.E, Lattice.T, CoherenceInput.toState]

end Coherence