import CoherenceLattice.Coherence.Lattice
import CoherenceLattice.Coherence.Regime

namespace Coherence
namespace Lattice

set_option linter.style.commandStart false
set_option linter.unusedSimpArgs false
noncomputable section

/-
Default Ψ-band thresholds (editable later):
  S0: Ψ < 0.2
  S1: 0.2 ≤ Ψ < 0.4
  S2: 0.4 ≤ Ψ < 0.6
  S3: 0.6 ≤ Ψ < 0.8
  S4: 0.8 ≤ Ψ
-/
def tau0 : ℝ := (1 : ℝ) / 5
def tau1 : ℝ := (2 : ℝ) / 5
def tau2 : ℝ := (3 : ℝ) / 5
def tau3 : ℝ := (4 : ℝ) / 5

/-- Classify a lattice State into regimes S0..S4 by Ψ bands. -/
def classify (s : State) : Coherence.Regime :=
  if psi s < tau0 then .s0
  else if psi s < tau1 then .s1
  else if psi s < tau2 then .s2
  else if psi s < tau3 then .s3
  else .s4

/-- A transition is valid if the next regime is in the adjacency list of the current regime. -/
def validTransition (s₁ s₂ : State) : Prop :=
  classify s₂ ∈ Coherence.adj (classify s₁)

/-- A state-path is valid if every consecutive pair is a validTransition. -/
def statePathValid : List State → Prop
  | [] => True
  | [_] => True
  | s₁ :: s₂ :: tl => validTransition s₁ s₂ ∧ statePathValid (s₂ :: tl)

/-- The induced regime path from a state path. -/
def regimePath (xs : List State) : List Coherence.Regime :=
  xs.map classify

/-- Reflexivity: staying put is always an allowed transition (by adjacency design). -/
lemma validTransition_refl (s : State) : validTransition s s := by
  unfold validTransition
  cases hs : classify s <;> simp [Coherence.adj, hs]

/-- If a state path is valid, then the mapped regime path is valid in the regime graph. -/
theorem validPath_of_statePathValid :
    ∀ xs : List State, statePathValid xs → Coherence.validPath (regimePath xs) := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp [statePathValid, regimePath, Coherence.validPath]
  | cons s tl ih =>
      cases tl with
      | nil =>
          intro _
          simp [statePathValid, regimePath, Coherence.validPath]
      | cons s2 tl2 =>
          intro h
          rcases h with ⟨h12, hrest⟩
          have ht : Coherence.validPath (regimePath (s2 :: tl2)) := ih hrest
          have h12' : classify s2 ∈ Coherence.adj (classify s) := by
            simpa [validTransition] using h12
          -- validPath (classify s :: classify s2 :: ...) is exactly (h12' ∧ ht)
          simpa [regimePath, Coherence.validPath] using And.intro h12' ht

end  -- closes `noncomputable section`

end Lattice
end Coherence