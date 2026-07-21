import RHFormalization.DBFFGate2WindowError
import RHFormalization.SeamCoreForm
import RHFormalization.AdmissibleFreeStageBound
import RHFormalization.AdmissibleFirstOrderVanish
import RHFormalization.AdmissibleResidualUniform
import RHFormalization.GalerkinCanonicalResidualBound
import Mathlib

/-!
# SeamCoreReduction — the corrected residual is banked ± seamCore

ROUTE CARD
1. Target: (i) EXACT: gate2 = FirstOrderWindow + BcorrWin − seamCore, so
   R_stage + Bcorr = Free + FirstOrderWindow + BcorrWin + Second − seamCore
   (compensatorM cancels). (ii) CONDITIONAL WIRING: corrected residual
   loc-bdd given seamCore control. The hypothesis is discharged ONLY by
   the P2-4 profile expansion (frozen rule 4) — never as a bare Prop.
2. Raw B on Ω? NO. B−M bare Prop? NO — hypothesis slot, profile-discharged.
3. Consumer: provider h_eps_bdd-side input → RcanCandidate → HtailExists.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **Gate2 in seam coordinates** (exact, every n, s). -/
theorem gate2WindowError_eq_window_add_bcorrwin_sub_seamCore (n : ℕ) (s : ℂ) :
    gate2WindowError n s
      = FirstOrderWindow n s + BcorrWin n s - seamCore n s := by
  unfold gate2WindowError Bcorr seamCore
  have hB : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (admR n))
          shiftedLaplaceHeatKernelC s := rfl
  rw [hB]; ring

/-- **The corrected residual is banked sectors minus seamCore** (exact on Ω). -/
theorem correctedResidual_eq_banked_sub_seamCore
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
        + Bcorr n s
      = admissibleFreeStage n s
        + FirstOrderWindow n s
        + BcorrWin n s
        + SecondResolventResidual n s
        - seamCore n s := by
  rw [correctedResidual_eq_free_add_gate2_add_second n hs,
    gate2WindowError_eq_window_add_bcorrwin_sub_seamCore]
  ring

/-- **Corrected residual loc-bdd from seamCore control.** The hypothesis
`hSC` is to be supplied ONLY by the P2-4/P2-5 profile expansion. -/
theorem correctedResidual_locbdd_of_seamCore
    (hSC : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
        ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
          + Bcorr n s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨CFr, hFr⟩ := admissibleFreeStage_uniform_bound K hK hKΩ
  obtain ⟨CW, hCW0, hWb⟩ := FirstOrderWindow_uniform_bound K hK hKΩ
  obtain ⟨Cw, hCw0, hw⟩ := BcorrWin_uniform_bound K hK hKΩ
  obtain ⟨CS, hCS0, hSb⟩ := SecondResolventResidual_uniform_bound K hK hKΩ
  obtain ⟨CT, hT⟩ := hSC K hK hKΩ
  refine ⟨CFr + CW + Cw + CS + CT, fun n s hs => ?_⟩
  have hsΩ : s ∈ Ω := hKΩ hs
  have hden : (1:ℝ) ≤ (n : ℝ) + 2 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hW1 : ‖FirstOrderWindow n s‖ ≤ CW := by
    have h := hWb n s hs
    have h2 : CW / ((n : ℝ) + 2) ≤ CW := div_le_self hCW0.le hden
    linarith
  have hS1 : ‖SecondResolventResidual n s‖ ≤ CS := by
    have h := hSb n s hs
    have h2 : CS / ((n : ℝ) + 2) ≤ CS := div_le_self hCS0.le hden
    linarith
  rw [correctedResidual_eq_banked_sub_seamCore n hsΩ]
  have h1 := hFr n s hs
  have h3 := hw n s hs
  have h5 := hT n s hs
  calc ‖admissibleFreeStage n s + FirstOrderWindow n s + BcorrWin n s
        + SecondResolventResidual n s - seamCore n s‖
      ≤ ‖admissibleFreeStage n s + FirstOrderWindow n s + BcorrWin n s
          + SecondResolventResidual n s‖ + ‖seamCore n s‖ := norm_sub_le _ _
    _ ≤ (‖admissibleFreeStage n s + FirstOrderWindow n s + BcorrWin n s‖
          + ‖SecondResolventResidual n s‖) + ‖seamCore n s‖ := by
        have := norm_add_le
          (admissibleFreeStage n s + FirstOrderWindow n s + BcorrWin n s)
          (SecondResolventResidual n s)
        linarith
    _ ≤ ((‖admissibleFreeStage n s + FirstOrderWindow n s‖ + ‖BcorrWin n s‖)
          + ‖SecondResolventResidual n s‖) + ‖seamCore n s‖ := by
        have := norm_add_le
          (admissibleFreeStage n s + FirstOrderWindow n s) (BcorrWin n s)
        linarith
    _ ≤ (((‖admissibleFreeStage n s‖ + ‖FirstOrderWindow n s‖) + ‖BcorrWin n s‖)
          + ‖SecondResolventResidual n s‖) + ‖seamCore n s‖ := by
        have := norm_add_le (admissibleFreeStage n s) (FirstOrderWindow n s)
        linarith
    _ ≤ CFr + CW + Cw + CS + CT := by linarith

#print axioms gate2WindowError_eq_window_add_bcorrwin_sub_seamCore
#print axioms correctedResidual_eq_banked_sub_seamCore
#print axioms correctedResidual_locbdd_of_seamCore

end

end RHFormalization
