
Theorem Map (Informal Claim ↔ Lean Formalization)
Informal claim (paper text)    Lean name (stable wrapper)    Where
Negative ΔS implies positive drive    Coherence.PaperGloss.Lemma_DrivePositive    CoherenceLattice/Coherence/Interpretation.lean
No-teleport: if    ΔΨ    < τ0 then transition is valid
ΔSyn ψ-step is regime-safe    Coherence.PaperGloss.Theorem_DeltaSynPsiStep_Safe    CoherenceLattice/Coherence/Dynamics.lean
ΔSyn E/T-step is regime-safe    Coherence.PaperGloss.Theorem_DeltaSynETStep_Safe    CoherenceLattice/Coherence/DynamicsET.lean
Bounded drift per E/T-step:    ΔΨ    ≤ τ0/2
If ΔS < 0 and ηE,ηT ≥ 0 then Ψ does not decrease under stepET    Coherence.PaperGloss.Lemma_PsiNondecreasing_stepET    CoherenceLattice/Coherence/Interpretation.lean
Iterating stepET yields a valid regime path    Coherence.PaperGloss.Corollary_TrajectoryET_ValidPath    CoherenceLattice/Coherence/Trajectory.lean
