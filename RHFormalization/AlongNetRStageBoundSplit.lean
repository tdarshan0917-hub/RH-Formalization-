import RHFormalization.PrimePerturbedDCANREMNetTarget

/-!
# AlongNetRStageBoundSplit — the splitter in the LIVE (along-net) shape

ROUTE CARD
1. Target: three-way split producing `PrimePerturbedAlignedAlongRStageBound`
   (∀ n along alpha — the net target file's own shape) from two along-net
   comparison bounds. The ∀-α `StageRBound` shape is the RETIRED over-strong
   target (frozen rule) and is NOT used.
2. Consumer: `primePerturbedAligned_h_loc_bdd_from_along_bound` →
   `primePerturbedAligned_hconv_from_montel` → the spine → flat terminus.
3. Raw B on Ω? NO (the split's G-leg carries the continued comparison).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- Along-net uniform Ω-compact bound for an arbitrary stage family. -/
def AlongNetBound (alpha : ℕ → DFiniteStage)
    (R : DFiniteStage → ℂ → ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ K, ‖R (alpha n) s‖ ≤ C

/-- **The along-net splitter**: R = F − B bounded along the net if both
comparison legs F − G and G − B are. -/
theorem alongNetBound_of_split
    (alpha : ℕ → DFiniteStage)
    (F G B R : DFiniteStage → ℂ → ℂ)
    (hR : ∀ α s, R α s = F α s - B α s)
    (hFG : AlongNetBound alpha (fun α s => F α s - G α s))
    (hGB : AlongNetBound alpha (fun α s => G α s - B α s)) :
    AlongNetBound alpha R := by
  intro K hKc hKΩ
  rcases hFG K hKc hKΩ with ⟨C1, hC1, h1⟩
  rcases hGB K hKc hKΩ with ⟨C2, hC2, h2⟩
  refine ⟨C1 + C2, add_nonneg hC1 hC2, ?_⟩
  intro n s hs
  rw [hR (alpha n) s]
  have hsplit : F (alpha n) s - B (alpha n) s
      = (F (alpha n) s - G (alpha n) s) + (G (alpha n) s - B (alpha n) s) := by
    ring
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add (h1 n s hs) (h2 n s hs))

/-- The splitter delivers the EXACT net-target Prop of the live route. -/
theorem primePerturbedAlignedAlongRStageBound_of_split
    {N : ℕ} (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (G : DFiniteStage → ℂ → ℂ)
    (hR : ∀ α s,
      (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s
        = (primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage α s
          - (primePerturbedOperatorLayerAligned μ).toStagePackage.B_stage α s)
    (hFG : AlongNetBound alpha (fun α s =>
      (primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage α s - G α s))
    (hGB : AlongNetBound alpha (fun α s =>
      G α s - (primePerturbedOperatorLayerAligned μ).toStagePackage.B_stage α s)) :
    PrimePerturbedAlignedAlongRStageBound μ alpha := by
  have h := alongNetBound_of_split alpha
    (fun α s => (primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage α s)
    G
    (fun α s => (primePerturbedOperatorLayerAligned μ).toStagePackage.B_stage α s)
    (fun α s => (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s)
    hR hFG hGB
  intro K hK hKΩ
  exact h K hK hKΩ

#print axioms alongNetBound_of_split
#print axioms primePerturbedAlignedAlongRStageBound_of_split

end

end RHFormalization
