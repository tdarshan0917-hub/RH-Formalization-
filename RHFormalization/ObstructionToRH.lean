import RHFormalization.HtailRouteCertificate
import RHFormalization.CanonicalRcanLocBddReduction
import RHFormalization.SeamCoreLocBddSkeleton
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-!
# ObstructionToRH — the terminal analytic object, certified to RH

hOB (Ω-continued obstruction bound) ⟹ Rcan locbdd ⟹ hSC ⟹ RH.
The four seam sectors are banked; the reduction and certificate are green.
After this file, THE project = one bound on `Rcan − core`.
-/

/-- **hSC from the obstruction bound**: the banked sectors convert an
Rcan bound into the seamCore bound. -/
theorem seamCore_locbdd_of_coreObstruction
    (hOB : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
        ‖canonicalRcanStage n s - galOmegaCore n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨CR, hR⟩ := canonicalRcanStage_locbdd_of_obstruction hOB K hK hKΩ
  obtain ⟨CFr, hFr⟩ := admissibleFreeStage_uniform_bound K hK hKΩ
  obtain ⟨CW, hCW0, hWb⟩ := FirstOrderWindow_uniform_bound K hK hKΩ
  obtain ⟨Cw, hCw0, hw⟩ := BcorrWin_uniform_bound K hK hKΩ
  obtain ⟨CS, hCS0, hSb⟩ := SecondResolventResidual_uniform_bound K hK hKΩ
  refine ⟨CFr + CW + Cw + CS + CR, fun n s hs => ?_⟩
  have hsΩ : s ∈ Ω := hKΩ hs
  have hden : (1:ℝ) ≤ (n : ℝ) + 2 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hW1 : ‖FirstOrderWindow n s‖ ≤ CW := by
    have h := hWb n s hs
    first
      | exact h
      | · have h2 : CW / ((n : ℝ) + 2) ≤ CW := div_le_self hCW0.le hden
          linarith
  have hS1 : ‖SecondResolventResidual n s‖ ≤ CS := by
    have h := hSb n s hs
    first
      | exact h
      | · have h2 : CS / ((n : ℝ) + 2) ≤ CS := div_le_self hCS0.le hden
          linarith
  have hkey := correctedResidual_eq_banked_sub_seamCore n hsΩ
  have hseam : seamCore n s
      = admissibleFreeStage n s + FirstOrderWindow n s + BcorrWin n s
        + SecondResolventResidual n s - canonicalRcanStage n s := by
    unfold canonicalRcanStage
    linear_combination hkey
  rw [hseam]
  have hRn : ‖canonicalRcanStage n s‖ ≤ CR := hR n s hs
  calc ‖admissibleFreeStage n s + FirstOrderWindow n s + BcorrWin n s
        + SecondResolventResidual n s - canonicalRcanStage n s‖
      ≤ ‖admissibleFreeStage n s + FirstOrderWindow n s + BcorrWin n s
          + SecondResolventResidual n s‖ + ‖canonicalRcanStage n s‖ :=
        norm_sub_le _ _
    _ ≤ (‖admissibleFreeStage n s‖ + ‖FirstOrderWindow n s‖
          + ‖BcorrWin n s‖ + ‖SecondResolventResidual n s‖)
        + ‖canonicalRcanStage n s‖ := by
        have h1 := norm_add_le (admissibleFreeStage n s) (FirstOrderWindow n s)
        have h2 := norm_add_le (admissibleFreeStage n s + FirstOrderWindow n s)
          (BcorrWin n s)
        have h3 := norm_add_le (admissibleFreeStage n s + FirstOrderWindow n s
          + BcorrWin n s) (SecondResolventResidual n s)
        linarith
    _ ≤ CFr + CW + Cw + CS + CR := by
        have := hFr n s hs
        have := hw n s hs
        linarith

/-- **THE TERMINAL CERTIFICATE: obstruction bound ⟹ RiemannHypothesis.** -/
theorem RH_of_coreObstruction
    (hOB : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
        ‖canonicalRcanStage n s - galOmegaCore n s‖ ≤ C) :
    RiemannHypothesis :=
  RH_of_seamCore_locbdd (seamCore_locbdd_of_coreObstruction hOB)

#print axioms seamCore_locbdd_of_coreObstruction
#print axioms RH_of_coreObstruction

end

end RHFormalization
