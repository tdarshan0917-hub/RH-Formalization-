import RHFormalization.DenseFctrBound
import RHFormalization.DBFFDeficitVanishing
import Mathlib

/-!
B(i)-6 part 2, installment 1 (GPT-signed three-output design):
the frozen rate object and the exact weight-integral identity.

denseFctrRate n = x^{-1/8}(1+log x) + x^{-3/4},  x = n+2
(= O(X^{-1/4}logX + X^{-3/2}), X = √x; the x^{-3/4} resolution term uses
ONLY the certified coarse ceiling denseL ≤ x³ — no sharper L bound.)

Weight integral: ∫₀^{admR n} e^{u/2} du = 2(e^{admR n /2} − 1)
≤ 2·(n+2)^{1/4}, exact by FTC + banked exp_admR.

Installment 2 (next): the compact rate theorem, denseFctrRate → 0,
and the rate-free compact-uniform corollary.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open Real intervalIntegral

/-- **The frozen B6 rate** (GPT amendment 1, Lean-friendly exact form). -/
noncomputable def denseFctrRate (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ (-(1:ℝ)/8) * (1 + Real.log ((n : ℝ) + 2))
    + ((n : ℝ) + 2) ^ (-(3:ℝ)/4)

theorem denseFctrRate_pos (n : ℕ) : 0 < denseFctrRate n := by
  unfold denseFctrRate
  have hx : (0:ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : (0:ℝ) < ((n : ℝ) + 2) ^ (-(1:ℝ)/8) := Real.rpow_pos_of_pos hx _
  have h2 : (0:ℝ) < ((n : ℝ) + 2) ^ (-(3:ℝ)/4) := Real.rpow_pos_of_pos hx _
  have hlog : (0:ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  nlinarith [mul_pos h1 (by linarith : (0:ℝ) < 1 + Real.log ((n : ℝ) + 2))]

/-- `e^{admR n / 2} = (n+2)^{1/4}` — the Lean-authoritative identity
(GPT: actual definitions authoritative over rendered Markdown). -/
theorem exp_half_admR_eq_rpow_quarter (n : ℕ) :
    Real.exp (admR n / 2) = ((n : ℝ) + 2) ^ ((1:ℝ)/4) := by
  have hx : (0:ℝ) < (n : ℝ) + 2 := by positivity
  show Real.exp (Real.log ((n : ℝ) + 2) / 2 / 2) = _
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- **The exact weight integral**: `∫₀^{admR n} e^{u/2} du
= 2(e^{admR n /2} − 1)` — FTC with antiderivative `2e^{u/2}`. -/
theorem weight_integral_eq (n : ℕ) :
    ∫ u in (0:ℝ)..(admR n), Real.exp (u/2)
      = 2 * (Real.exp (admR n / 2) - 1) := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) (admR n),
      HasDerivAt (fun t : ℝ => 2 * Real.exp (t/2))
        (Real.exp (u/2)) u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => t/2) (1/2) u := by
      simpa using (hasDerivAt_id u).div_const 2
    have h2 := (Real.hasDerivAt_exp (u/2)).comp u h1
    have h3 := h2.const_mul (2:ℝ)
    convert h3 using 1
    ring
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (u/2))
      MeasureTheory.volume 0 (admR n) :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp
  ring

/-- **The weight bound**: `∫₀^{admR n} e^{u/2} du ≤ 2(n+2)^{1/4}`
(= 2√X in X-variables). -/
theorem weight_integral_le (n : ℕ) :
    ∫ u in (0:ℝ)..(admR n), Real.exp (u/2) ≤ 2 * ((n : ℝ) + 2) ^ ((1:ℝ)/4) := by
  rw [weight_integral_eq, ← exp_half_admR_eq_rpow_quarter]
  have := Real.exp_pos (admR n / 2)
  linarith

#print axioms denseFctrRate_pos
#print axioms exp_half_admR_eq_rpow_quarter
#print axioms weight_integral_eq
#print axioms weight_integral_le

end

end RHFormalization
