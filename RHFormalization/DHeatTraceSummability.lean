import Mathlib
import RHFormalization.Basic

/-!
# RHFormalization.DHeatTraceSummability

A small theorem-backed spectral summability layer for the D-side heat trace.

This file does not prove the full Appendix-D trace-class operator theorem.
It proves the series-level fact used in the fixed-stage heat trace argument:

if the finite-stage eigenvalues grow at least linearly, then
`∑ exp (-t * lam n)` is summable for every `t > 0`.
-/

namespace RHFormalization

noncomputable section

/--
If `lam n / a ≥ n` with `a > 0`, then the heat series
`∑ n, exp (-t * lam n)` is summable for every `t > 0`.

This is a theorem-backed spectral summability proxy for fixed-stage heat trace legality.
-/
theorem summable_heat_exp_of_linear_lower
    {lam : ℕ → ℝ}
    {a t : ℝ}
    (ha : 0 < a)
    (ht : 0 < t)
    (hlam : ∀ n : ℕ, (n : ℝ) ≤ lam n / a) :
    Summable (fun n : ℕ => Real.exp (-t * lam n)) := by
  have hta : 0 < t * a := mul_pos ht ha
  have hc : -(t * a) < 0 := by
    nlinarith
  have hsum :
      Summable (fun n : ℕ => Real.exp (-(t * a) * (lam n / a))) :=
    Real.summable_exp_nat_mul_of_ge (c := -(t * a)) hc hlam
  exact hsum.congr (fun n => by
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have harg : -(t * a) * (lam n / a) = -t * lam n := by
      field_simp [ha_ne]
    rw [harg])

end

end RHFormalization
