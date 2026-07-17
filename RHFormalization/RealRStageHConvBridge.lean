import RHFormalization.ArithmeticPrimeShiftedLaplaceBStage
import RHFormalization.CanonicalPrimePowerSummabilityMajorant
import RHFormalization.ShiftedLaplaceTLUFromLocalMTest
import RHFormalization.FHHoloFromStages
import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.PrimePerturbedAlignedHConvTarget
import Mathlib

/-!
# BRIDGE: h_conv for the REAL R_stage = F_stage - B_stage (NOT designed, NOT B-only).
GPT's trap: M-test gives B_stage -> B_can. R_stage = F - B needs the F-side too.
This forces the F-side convergence obligation into the open. Any sorry IS the gap.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- The real residual h_conv, decomposed into F-side and B-side convergence.
    R_stage = F_stage - B_stage, so R_stage -> F_H - B_can needs BOTH. -/
theorem real_R_stage_h_conv_from_FB_conv
    {N : ℕ} (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (F_H B_can : ℂ → ℂ)
    -- B-side: the banked M-test gives this (B_stage -> B_can)
    (hB_conv : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K →
        dist (arithmeticShiftedLaplaceBStage (alpha n) s) (B_can s) < ε)
    -- F-side: THE OBLIGATION — is this banked or missing? (D.5.10W content)
    (hF_conv : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K →
        dist ((primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (alpha n) s) (F_H s) < ε) :
    PrimePerturbedAlignedHConv μ alpha (fun s => F_H s - B_can s) := by
  intro K hK hKΩ ε hε
  -- R_stage = F_stage - B_stage; want dist (F-B) (F_H - B_can) < ε
  -- triangle: ≤ dist F F_H + dist B B_can; take each < ε/2
  have hBε := hB_conv K hK hKΩ (ε/2) (by linarith)
  have hFε := hF_conv K hK hKΩ (ε/2) (by linarith)
  filter_upwards [hBε, hFε] with n hBn hFn s hs
  show dist ((primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s)
        (F_H s - B_can s) < ε
  have hRsplit :
      (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s
        = (primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (alpha n) s
          - arithmeticShiftedLaplaceBStage (alpha n) s := by
    rfl
  rw [hRsplit]
  have hFs := hFn s hs
  have hBs := hBn s hs
  simp only [dist_eq_norm] at hFs hBs ⊢
  have hregroup :
      ((primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (alpha n) s
          - arithmeticShiftedLaplaceBStage (alpha n) s) - (F_H s - B_can s)
        = ((primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (alpha n) s - F_H s)
          - (arithmeticShiftedLaplaceBStage (alpha n) s - B_can s) := by ring
  rw [hregroup]
  calc ‖((primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (alpha n) s - F_H s)
          - (arithmeticShiftedLaplaceBStage (alpha n) s - B_can s)‖
      ≤ ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.F_stage (alpha n) s - F_H s‖
          + ‖arithmeticShiftedLaplaceBStage (alpha n) s - B_can s‖ := norm_sub_le _ _
    _ < ε/2 + ε/2 := add_lt_add hFs hBs
    _ = ε := by ring

end
end RHFormalization

#print axioms RHFormalization.real_R_stage_h_conv_from_FB_conv
