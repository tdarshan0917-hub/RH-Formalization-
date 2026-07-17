-- SENTINEL: R2-v1
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open MeasureTheory Real Set

/-!
# Sqrt-form right-tail Gaussian bound (defect-gate R2)

`∫_{Ioi R} e^{−b·u²} ≤ e^{−bR²/2}·√(2π/b)`.

Complements the banked `gaussian_Ioi_tail_le` (which gives `e^{−bR²}/(bR)`,
sharp for large `R` but useless when the `t`-integration hits `1/(tM)` at
`t → 0`). This form keeps a full Gaussian factor in `t`, so the short-time
Laplace piece integrates to `O(1/M)` — the rate that closes the gate.

Route: on `Ioi R` with `0 ≤ R`, pointwise `u² ≥ R²/2 + u²/2`, so
`e^{−bu²} ≤ e^{−bR²/2}·e^{−(b/2)u²}`; integrate, pull the constant, extend
to the whole line, evaluate by `integral_gaussian`.
-/

theorem gaussian_Ioi_tail_le_sqrt
    (b R : ℝ) (hb : 0 < b) (hR : 0 ≤ R) :
    ∫ u in Ioi R, Real.exp (-b * u ^ 2)
      ≤ Real.exp (-(b * R ^ 2) / 2) * Real.sqrt (2 * π / b) := by
  have hb2 : 0 < b / 2 := by positivity
  have hpt : ∀ u ∈ Ioi R, Real.exp (-b * u ^ 2)
      ≤ Real.exp (-(b * R ^ 2) / 2) * Real.exp (-(b / 2) * u ^ 2) := by
    intro u hu
    have hu' : R < u := hu
    have hRu : R ^ 2 ≤ u ^ 2 := by nlinarith [hu'.le, hR]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hRu)]
  have hint1 : IntegrableOn (fun u => Real.exp (-b * u ^ 2)) (Ioi R) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have hint2 : IntegrableOn
      (fun u => Real.exp (-(b * R ^ 2) / 2) * Real.exp (-(b / 2) * u ^ 2))
      (Ioi R) :=
    ((integrable_exp_neg_mul_sq hb2).const_mul _).integrableOn
  calc ∫ u in Ioi R, Real.exp (-b * u ^ 2)
      ≤ ∫ u in Ioi R,
          Real.exp (-(b * R ^ 2) / 2) * Real.exp (-(b / 2) * u ^ 2) := by
        first
          | exact setIntegral_mono_on hint1 hint2 measurableSet_Ioi hpt
          | exact MeasureTheory.setIntegral_mono_on hint1 hint2
              measurableSet_Ioi hpt
          | exact setIntegral_mono_on hint1 hint2 measurableSet_Ioi
              (fun u hu => hpt u hu)
    _ = Real.exp (-(b * R ^ 2) / 2)
          * ∫ u in Ioi R, Real.exp (-(b / 2) * u ^ 2) := by
        rw [integral_const_mul]
    _ ≤ Real.exp (-(b * R ^ 2) / 2)
          * ∫ u : ℝ, Real.exp (-(b / 2) * u ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact setIntegral_le_integral (integrable_exp_neg_mul_sq hb2)
          (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))
    _ = Real.exp (-(b * R ^ 2) / 2) * Real.sqrt (π / (b / 2)) := by
        rw [integral_gaussian]
    _ = Real.exp (-(b * R ^ 2) / 2) * Real.sqrt (2 * π / b) := by
        congr 1
        field_simp

#print axioms gaussian_Ioi_tail_le_sqrt

end RHFormalization
