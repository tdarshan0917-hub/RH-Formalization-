import RHFormalization.DBFFGate2WindowError
import RHFormalization.CompensatedBTailReduction
import Mathlib

/-!
# AdmissibleFreeStageBound — the free sector closes from banked bounds

ROUTE CARD
1. Target: admissibleFreeStage compact-uniformly bounded on Ω-compacts.
   Triangle inequality: Free = F_stage − FirstOrderWindow − Second, with
   F banked bounded and the other two banked VANISHING (≤ C/(n+2) ≤ C).
   NOT Hfree (free − M): unsatisfiable, untargeted.
2. Consequence with SeamCoreForm: sole open object is seamCore.
3. Raw B on Ω? NO. B−M as bare Prop? NO.
4. Consumer: P2-5 assembly.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

theorem admissibleFreeStage_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖admissibleFreeStage n s‖ ≤ C := by
  obtain ⟨CF, _hCF0, hF⟩ := F_stage_uniform_bound_on_compacts K hK hKΩ
  obtain ⟨CW, hCW0, hWb⟩ := FirstOrderWindow_uniform_bound K hK hKΩ
  obtain ⟨CS, hCS0, hSb⟩ := SecondResolventResidual_uniform_bound K hK hKΩ
  refine ⟨CF + CW + CS, fun n s hs => ?_⟩
  have hsΩ : s ∈ Ω := hKΩ hs
  have hden : (1:ℝ) ≤ (n : ℝ) + 2 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hW1 : ‖FirstOrderWindow n s‖ ≤ CW := by
    have h := hWb n s hs
    have h2 : CW / ((n : ℝ) + 2) ≤ CW :=
      div_le_self hCW0.le hden
    linarith
  have hS1 : ‖SecondResolventResidual n s‖ ≤ CS := by
    have h := hSb n s hs
    have h2 : CS / ((n : ℝ) + 2) ≤ CS :=
      div_le_self hCS0.le hden
    linarith
  have hid : admissibleFreeStage n s
      = galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - FirstOrderWindow n s - SecondResolventResidual n s := by
    have hF' : galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        = admissibleFreeStage n s + FadmPrimeStage n s := by
      unfold FadmPrimeStage; ring
    have hsplit := FadmPrimeStage_eq_first_plus_second n hsΩ
    rw [hF', hsplit]; ring
  rw [hid]
  calc ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - FirstOrderWindow n s - SecondResolventResidual n s‖
      ≤ ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - FirstOrderWindow n s‖ + ‖SecondResolventResidual n s‖ :=
        norm_sub_le _ _
    _ ≤ (‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s‖
          + ‖FirstOrderWindow n s‖) + ‖SecondResolventResidual n s‖ := by
        have := norm_sub_le
          (galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s)
          (FirstOrderWindow n s)
        linarith
    _ ≤ (CF + CW) + CS := by
        have h1 := hF n s hs
        linarith
    _ = CF + CW + CS := by ring

#print axioms admissibleFreeStage_uniform_bound

end

end RHFormalization
