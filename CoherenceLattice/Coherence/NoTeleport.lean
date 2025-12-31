import CoherenceLattice.Coherence.Classifier

namespace Coherence
namespace Lattice

set_option linter.style.commandStart false
set_option linter.unusedSimpArgs false
noncomputable section

-- handy arithmetic facts about thresholds
lemma tau0_add_tau0 : tau0 + tau0 = tau1 := by unfold tau0 tau1; norm_num
lemma tau1_add_tau0 : tau1 + tau0 = tau2 := by unfold tau0 tau1 tau2; norm_num
lemma tau2_add_tau0 : tau2 + tau0 = tau3 := by unfold tau0 tau2 tau3; norm_num
lemma tau1_sub_tau0 : tau1 - tau0 = tau0 := by unfold tau0 tau1; norm_num
lemma tau2_sub_tau0 : tau2 - tau0 = tau1 := by unfold tau0 tau1 tau2; norm_num
lemma tau3_sub_tau0 : tau3 - tau0 = tau2 := by unfold tau0 tau2 tau3; norm_num
lemma tau0_le_tau1 : tau0 ≤ tau1 := by unfold tau0 tau1; norm_num
lemma tau0_le_tau2 : tau0 ≤ tau2 := by unfold tau0 tau2; norm_num
lemma tau1_le_tau2 : tau1 ≤ tau2 := by unfold tau1 tau2; norm_num

/--
No-teleport theorem:
If Ψ changes by less than τ₀ (= 0.2), then the induced regime transition is valid.
-/
theorem validTransition_of_abs_lt_tau0 {s₁ s₂ : State}
    (h : |psi s₂ - psi s₁| < tau0) :
    validTransition s₁ s₂ := by
  unfold validTransition
  have habs := abs_lt.mp h
  have hlower : psi s₁ - tau0 < psi s₂ := by
    linarith [habs.1]
  have hupper : psi s₂ < psi s₁ + tau0 := by
    linarith [habs.2]

  -- split on which Ψ-band s₁ is in
  by_cases h0 : psi s₁ < tau0
  · -- s₁ in S0 → s₂ can only be S0 or S1
    have hs1 : classify s₁ = .s0 := by simp [classify, h0]
    have hpsi2_lt_tau1 : psi s₂ < tau1 := by
      have : psi s₂ < tau0 + tau0 := by linarith [hupper, h0]
      simpa [tau0_add_tau0] using this
    by_cases h0' : psi s₂ < tau0
    · have hs2 : classify s₂ = .s0 := by simp [classify, h0']
      simp [hs1, hs2, Coherence.adj]
    · have hs2 : classify s₂ = .s1 := by simp [classify, h0', hpsi2_lt_tau1]
      simp [hs1, hs2, Coherence.adj]

  · by_cases h1 : psi s₁ < tau1
    · -- s₁ in S1 → s₂ can be S0,S1,S2
      have hs1 : classify s₁ = .s1 := by simp [classify, h0, h1]
      have hpsi2_lt_tau2 : psi s₂ < tau2 := by
        have : psi s₂ < tau1 + tau0 := by linarith [hupper, h1]
        simpa [tau1_add_tau0] using this
      by_cases h0' : psi s₂ < tau0
      · have hs2 : classify s₂ = .s0 := by simp [classify, h0']
        simp [hs1, hs2, Coherence.adj]
      · by_cases h1' : psi s₂ < tau1
        · have hs2 : classify s₂ = .s1 := by simp [classify, h0', h1']
          simp [hs1, hs2, Coherence.adj]
        · have hs2 : classify s₂ = .s2 := by simp [classify, h0', h1', hpsi2_lt_tau2]
          simp [hs1, hs2, Coherence.adj]

    · by_cases h2 : psi s₁ < tau2
      · -- s₁ in S2 → s₂ can be S1,S2,S3 (and cannot be S0)
        have hs1 : classify s₁ = .s2 := by simp [classify, h0, h1, h2]
        have hpsi1_ge_tau1 : tau1 ≤ psi s₁ := le_of_not_gt h1
        have hle : tau0 ≤ psi s₁ - tau0 := by
          have : tau1 - tau0 ≤ psi s₁ - tau0 := sub_le_sub_right hpsi1_ge_tau1 tau0
          simpa [tau1_sub_tau0] using this
        have hpsi2_gt_tau0 : tau0 < psi s₂ := lt_of_le_of_lt hle hlower
        have hnot0' : ¬ psi s₂ < tau0 := not_lt.mpr (le_of_lt hpsi2_gt_tau0)
        have hpsi2_lt_tau3 : psi s₂ < tau3 := by
          have : psi s₂ < tau2 + tau0 := by linarith [hupper, h2]
          simpa [tau2_add_tau0] using this
        by_cases h1' : psi s₂ < tau1
        · have hs2 : classify s₂ = .s1 := by simp [classify, hnot0', h1']
          simp [hs1, hs2, Coherence.adj]
        · by_cases h2' : psi s₂ < tau2
          · have hs2 : classify s₂ = .s2 := by simp [classify, hnot0', h1', h2']
            simp [hs1, hs2, Coherence.adj]
          · have hs2 : classify s₂ = .s3 := by simp [classify, hnot0', h1', h2', hpsi2_lt_tau3]
            simp [hs1, hs2, Coherence.adj]

      · by_cases h3 : psi s₁ < tau3
        · -- s₁ in S3 → s₂ can be S2,S3,S4 (and cannot be S0,S1)
          have hs1 : classify s₁ = .s3 := by simp [classify, h0, h1, h2, h3]
          have hpsi1_ge_tau2 : tau2 ≤ psi s₁ := le_of_not_gt h2
          have hle : tau1 ≤ psi s₁ - tau0 := by
            have : tau2 - tau0 ≤ psi s₁ - tau0 := sub_le_sub_right hpsi1_ge_tau2 tau0
            simpa [tau2_sub_tau0] using this
          have hpsi2_gt_tau1 : tau1 < psi s₂ := lt_of_le_of_lt hle hlower
          have hnot0' : ¬ psi s₂ < tau0 :=
            not_lt.mpr (le_trans tau0_le_tau1 (le_of_lt hpsi2_gt_tau1))
          have hnot1' : ¬ psi s₂ < tau1 := not_lt.mpr (le_of_lt hpsi2_gt_tau1)
          by_cases h2' : psi s₂ < tau2
          · have hs2 : classify s₂ = .s2 := by simp [classify, hnot0', hnot1', h2']
            simp [hs1, hs2, Coherence.adj]
          · by_cases h3' : psi s₂ < tau3
            · have hs2 : classify s₂ = .s3 := by simp [classify, hnot0', hnot1', h2', h3']
              simp [hs1, hs2, Coherence.adj]
            · have hs2 : classify s₂ = .s4 := by simp [classify, hnot0', hnot1', h2', h3']
              simp [hs1, hs2, Coherence.adj]

        · -- s₁ in S4 → s₂ can be S3 or S4 (and cannot be S0,S1,S2)
          have hs1 : classify s₁ = .s4 := by simp [classify, h0, h1, h2, h3]
          have hpsi1_ge_tau3 : tau3 ≤ psi s₁ := le_of_not_gt h3
          have hle : tau2 ≤ psi s₁ - tau0 := by
            have : tau3 - tau0 ≤ psi s₁ - tau0 := sub_le_sub_right hpsi1_ge_tau3 tau0
            simpa [tau3_sub_tau0] using this
          have hpsi2_gt_tau2 : tau2 < psi s₂ := lt_of_le_of_lt hle hlower
          have hnot0' : ¬ psi s₂ < tau0 :=
            not_lt.mpr (le_trans tau0_le_tau2 (le_of_lt hpsi2_gt_tau2))
          have hnot1' : ¬ psi s₂ < tau1 :=
            not_lt.mpr (le_trans tau1_le_tau2 (le_of_lt hpsi2_gt_tau2))
          have hnot2' : ¬ psi s₂ < tau2 := not_lt.mpr (le_of_lt hpsi2_gt_tau2)
          by_cases h3' : psi s₂ < tau3
          · have hs2 : classify s₂ = .s3 := by simp [classify, hnot0', hnot1', hnot2', h3']
            simp [hs1, hs2, Coherence.adj]
          · have hs2 : classify s₂ = .s4 := by simp [classify, hnot0', hnot1', hnot2', h3']
            simp [hs1, hs2, Coherence.adj]

end  -- noncomputable section

end Lattice
end Coherence