import RHFormalization.DOperatorExport

namespace RHFormalization
noncomputable section
open Complex

/-- The exact shape of the real D-side `h_R_stage_bound`: uniform Ω-compact bound
over ALL finite Appendix-D stages. Independent of `designedY`. -/
def StageRBound (R : DFiniteStage → ℂ → ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : DFiniteStage, ∀ s ∈ K, ‖R α s‖ ≤ C

/-- **Main attack splitter for `h_R_stage_bound`.** Decompose the real residual
through an intermediate comparison object `G`; if both pieces are uniformly bounded
on Ω-compacts over all stages, the full R-stage bound follows. Non-placeholder
replacement for the fake `R_stage = 0` route. -/
theorem StageRBound_of_split
    (F G B R : DFiniteStage → ℂ → ℂ)
    (hR : ∀ α s, R α s = F α s - B α s)
    (hFG : StageRBound (fun α s => F α s - G α s))
    (hGB : StageRBound (fun α s => G α s - B α s)) :
    StageRBound R := by
  intro K hKc hKΩ
  rcases hFG K hKc hKΩ with ⟨C1, hC1, h1⟩
  rcases hGB K hKc hKΩ with ⟨C2, hC2, h2⟩
  refine ⟨C1 + C2, add_nonneg hC1 hC2, ?_⟩
  intro α s hs
  rw [hR α s]
  have hsplit : F α s - B α s = (F α s - G α s) + (G α s - B α s) := by ring
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add (h1 α s hs) (h2 α s hs))

#print axioms StageRBound
#print axioms StageRBound_of_split
end
end RHFormalization
