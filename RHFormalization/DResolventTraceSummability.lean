import Mathlib
import RHFormalization.Basic

/-!
# RHFormalization.DResolventTraceSummability

Theorem-backed p-series comparison layer for D-side resolvent trace legality.

This file does not prove the full Appendix-D resolvent trace theorem.  It proves
the summability comparison lemma needed for the spectral-series route:

if a complex sequence is bounded in norm by a constant multiple of `1 / n^2`,
then the sequence is summable.
-/

namespace RHFormalization

noncomputable section

/--
The real p-series `∑ 1 / n^2` is summable.

Lean treats the `n = 0` term harmlessly because division by zero in a field is defined
as zero.
-/
theorem summable_one_div_nat_sq :
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
  exact (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)

/--
If a complex sequence is norm-bounded by `C / n^2`, then it is summable.

This is the abstract comparison theorem needed for resolvent trace legality once
the finite-stage spectral estimate supplies the required bound.
-/
theorem summable_complex_of_norm_le_const_one_div_nat_sq
    {f : ℕ → ℂ}
    {C : ℝ}
    (hC : 0 ≤ C)
    (hbound :
      ∀ n : ℕ,
        ‖f n‖ ≤ C * ((1 : ℝ) / (n : ℝ) ^ 2)) :
    Summable f := by
  have hs_base :
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    summable_one_div_nat_sq

  have hs_dom :
      Summable (fun n : ℕ => C * ((1 : ℝ) / (n : ℝ) ^ 2)) :=
    hs_base.mul_left C

  have hs_norm :
      Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le
      (fun n => norm_nonneg (f n))
      hbound
      hs_dom

  exact hs_norm.of_norm

end

end RHFormalization
