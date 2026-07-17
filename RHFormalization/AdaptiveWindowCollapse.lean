-- SENTINEL: adaptive-window-collapse-v1
import RHFormalization.SealReductionEndpoint
import RHFormalization.GalerkinCanonicalResidualBound
import RHFormalization.AdaptiveWeightedDefectSum
import Mathlib

/-!
# hW COLLAPSED — the adaptive window bound from the banked admissible one
Exact identity: adaptiveBcorrWin = (admL/adaptiveL)·BcorrWin (termwise, same
weights and kernels, only the window denominator differs). Ratio ∈ (0,1]
(admL_le_adaptiveL). BcorrWin_uniform_bound is banked. ⟹ hW proved, and
RH ⇐ hP ALONE: ‖2·(free paired transform) − compensatorM‖ ≤ C(K).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology BigOperators

/-- The exact window-ratio identity. -/
theorem adaptiveBcorrWin_eq_ratio_mul (c : ℝ) (n : ℕ) (s : ℂ) :
    adaptiveBcorrWin c n s
      = ((admL n / adaptiveL c n : ℝ) : ℂ) * BcorrWin n s := by
  unfold adaptiveBcorrWin BcorrWin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hadm : (0:ℝ) < admL n := admL_pos' n
  have hadp : (0:ℝ) < adaptiveL c n :=
    lt_of_lt_of_le (by norm_num) (eight_le_adaptiveL c n)
  have hcast : ((q.center / (2 * adaptiveL c n) : ℝ) : ℂ)
      = ((admL n / adaptiveL c n : ℝ) : ℂ)
        * ((q.center / (2 * admL n) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [hcast]
  ring

/-- **hW discharged**: adaptive window uniformly bounded on Ω-compacts. -/
theorem adaptiveBcorrWin_uniform_bound (c : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ Cw : ℝ, ∀ n, ∀ s ∈ K, ‖adaptiveBcorrWin c n s‖ ≤ Cw := by
  obtain ⟨Cw, hCw0, hw⟩ := BcorrWin_uniform_bound K hK hKΩ
  refine ⟨Cw, fun n s hs => ?_⟩
  rw [adaptiveBcorrWin_eq_ratio_mul, norm_mul]
  have hadm : (0:ℝ) < admL n := admL_pos' n
  have hadp : (0:ℝ) < adaptiveL c n :=
    lt_of_lt_of_le (by norm_num) (eight_le_adaptiveL c n)
  have hratio : ‖((admL n / adaptiveL c n : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hadm.le hadp.le)]
    rw [div_le_one hadp]
    exact admL_le_adaptiveL c n
  calc ‖((admL n / adaptiveL c n : ℝ) : ℂ)‖ * ‖BcorrWin n s‖
      ≤ 1 * ‖BcorrWin n s‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ = ‖BcorrWin n s‖ := one_mul _
    _ ≤ Cw := hw n s hs

/-- **RH FROM hP ALONE** — the single-hypothesis paired-transform endpoint. -/
theorem RH_from_pairedTransform_only (c : ℝ)
    (hP : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
          ‖(2:ℂ) * adaptiveFreePairedTransform c n s - compensatorM n s‖ ≤ Cp) :
    RiemannHypothesis :=
  RH_from_pairedTransform_locbdd c
    (fun K hK hKΩ => adaptiveBcorrWin_uniform_bound c K hK hKΩ) hP

#print axioms adaptiveBcorrWin_eq_ratio_mul
#print axioms adaptiveBcorrWin_uniform_bound
#print axioms RH_from_pairedTransform_only

end

end RHFormalization
