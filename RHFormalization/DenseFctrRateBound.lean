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

/-- x-positivity workhorse. -/
private theorem hx2 (n : ℕ) : (2:ℝ) ≤ (n : ℝ) + 2 := by
  have := Nat.cast_nonneg (α := ℝ) n; linarith

private theorem hxpos (n : ℕ) : (0:ℝ) < (n : ℝ) + 2 := by positivity

/-- Term (i): `(1/2L)((R/c)(π/2) + 1/c²) ≤ (π/(4c) + 1/c²)·x^{-3/8}(1+log x)`. -/
theorem perSpike_term1_le (n : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    (1 / (2 * denseL n)) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2)
      ≤ (Real.pi / (4 * c₀) + 1 / c₀^2)
          * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2))) := by
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have hlog : (0:ℝ) ≤ Real.log ((n:ℝ)+2) :=
    Real.log_nonneg (by linarith [hx2 n])
  have hRnn : (0:ℝ) ≤ admR n := (admR_pos n).le
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  -- 1/(2L) ≤ x^{-3/8} (from the floor x^{3/8} ≤ L, and 2L ≥ L)
  have hLfloor := rpow_le_denseL n
  have hxr : (0:ℝ) < ((n:ℝ)+2) ^ ((3:ℝ)/8) := Real.rpow_pos_of_pos (hxpos n) _
  have hinv2L : 1 / (2 * denseL n) ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/8) := by
    have hexp : ((n:ℝ)+2) ^ (-(3:ℝ)/8) = (((n:ℝ)+2) ^ ((3:ℝ)/8))⁻¹ := by
      rw [← Real.rpow_neg (hxpos n).le]
      norm_num
    rw [hexp, ← one_div]
    have h2L : ((n:ℝ)+2) ^ ((3:ℝ)/8) ≤ 2 * denseL n := by nlinarith
    exact one_div_le_one_div_of_le hxr h2L
  -- (R/c)(π/2) + 1/c² ≤ (π/(4c) + 1/c²)·(1+log x), since R = (log x)/2
  have hbrack : (admR n / c₀) * (Real.pi / 2) + 1 / c₀^2
      ≤ (Real.pi / (4 * c₀) + 1 / c₀^2) * (1 + Real.log ((n:ℝ)+2)) := by
    have hR : admR n = Real.log ((n:ℝ)+2) / 2 := rfl
    rw [hR]
    have h1 : (0:ℝ) ≤ 1 / c₀^2 := by positivity
    have h2 : (0:ℝ) ≤ Real.pi / (4 * c₀) := by positivity
    have hkey : Real.log ((n:ℝ)+2) / 2 / c₀ * (Real.pi / 2)
        = Real.pi / (4 * c₀) * Real.log ((n:ℝ)+2) := by
      field_simp
      ring
    rw [hkey]
    nlinarith [mul_nonneg h1 hlog]
  have hbr0 : (0:ℝ) ≤ (admR n / c₀) * (Real.pi / 2) + 1 / c₀^2 := by positivity
  have hxneg : (0:ℝ) ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/8) :=
    Real.rpow_nonneg (hxpos n).le _
  calc (1 / (2 * denseL n)) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2)
      ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/8) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2) :=
        mul_le_mul_of_nonneg_right hinv2L hbr0
    _ ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/8)
          * ((Real.pi / (4 * c₀) + 1 / c₀^2) * (1 + Real.log ((n:ℝ)+2))) :=
        mul_le_mul_of_nonneg_left hbrack hxneg
    _ = (Real.pi / (4 * c₀) + 1 / c₀^2)
          * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2))) := by ring

/-- Term (ii): `L/(2cπ²N) ≤ (1/(2cπ²))·x^{-1}` — the resolution term,
using ONLY the coarse ceiling `denseL ≤ x³` and `N = x⁴`. -/
theorem perSpike_term2_le (n : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    denseL n / (2 * c₀ * Real.pi^2 * (denseN n : ℝ))
      ≤ (1 / (2 * c₀ * Real.pi^2)) * (((n:ℝ)+2) ^ (-(1:ℝ))) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hN : ((denseN n : ℕ) : ℝ) = ((n:ℝ)+2)^4 := denseN_cast n
  have hx4 : (0:ℝ) < ((n:ℝ)+2)^4 := by positivity
  have hden : (0:ℝ) < 2 * c₀ * Real.pi^2 := by positivity
  rw [Real.rpow_neg (hxpos n).le, Real.rpow_one]
  rw [div_le_iff₀ (by rw [hN]; positivity)]
  rw [show (1 / (2 * c₀ * Real.pi^2)) * (((n:ℝ)+2))⁻¹
        * (2 * c₀ * Real.pi^2 * ((denseN n : ℕ) : ℝ))
      = ((denseN n : ℕ) : ℝ) / ((n:ℝ)+2) from by field_simp]
  rw [hN]
  have hcube := denseL_le_cube n
  rw [show ((n:ℝ)+2)^4 / ((n:ℝ)+2) = ((n:ℝ)+2)^3 from by
    field_simp]
  exact hcube

/-- Term (iii): `(1/(2Lcπ))(1+log N) ≤ (4/(2cπ))·x^{-3/8}(1+log x)`,
using `log N = log(x⁴) = 4 log x` and the L floor. -/
theorem perSpike_term3_le (n : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    (1 / (2 * denseL n * c₀ * Real.pi)) * (1 + Real.log (denseN n : ℝ))
      ≤ (4 / (2 * c₀ * Real.pi))
          * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2))) := by
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hlog : (0:ℝ) ≤ Real.log ((n:ℝ)+2) :=
    Real.log_nonneg (by linarith [hx2 n])
  have hN : ((denseN n : ℕ) : ℝ) = ((n:ℝ)+2)^4 := denseN_cast n
  have hlogN : Real.log ((denseN n : ℕ) : ℝ) = 4 * Real.log ((n:ℝ)+2) := by
    rw [hN, Real.log_pow]
    push_cast
    ring
  have h1logN : 1 + Real.log ((denseN n : ℕ) : ℝ)
      ≤ 4 * (1 + Real.log ((n:ℝ)+2)) := by
    rw [hlogN]; linarith
  have hLfloor := rpow_le_denseL n
  have hxr : (0:ℝ) < ((n:ℝ)+2) ^ ((3:ℝ)/8) := Real.rpow_pos_of_pos (hxpos n) _
  have hinvL : 1 / (2 * denseL n * c₀ * Real.pi)
      ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 / (2 * c₀ * Real.pi)) := by
    have hexp : ((n:ℝ)+2) ^ (-(3:ℝ)/8) = (((n:ℝ)+2) ^ ((3:ℝ)/8))⁻¹ := by
      rw [← Real.rpow_neg (hxpos n).le]
      norm_num
    have hstep : 1 / (2 * denseL n * c₀ * Real.pi)
        ≤ 1 / (2 * ((n:ℝ)+2) ^ ((3:ℝ)/8) * c₀ * Real.pi) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hcp : (0:ℝ) < c₀ * Real.pi := mul_pos hc₀ hπ
      nlinarith [mul_le_mul_of_nonneg_right hLfloor hcp.le]
    calc 1 / (2 * denseL n * c₀ * Real.pi)
        ≤ 1 / (2 * ((n:ℝ)+2) ^ ((3:ℝ)/8) * c₀ * Real.pi) := hstep
      _ = ((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 / (2 * c₀ * Real.pi)) := by
          rw [hexp]
          field_simp
  have h1N0 : (0:ℝ) ≤ 1 + Real.log ((denseN n : ℕ) : ℝ) := by
    rw [hlogN]; linarith
  calc (1 / (2 * denseL n * c₀ * Real.pi)) * (1 + Real.log ((denseN n : ℕ) : ℝ))
      ≤ (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 / (2 * c₀ * Real.pi)))
          * (1 + Real.log ((denseN n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hinvL h1N0
    _ ≤ (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 / (2 * c₀ * Real.pi)))
          * (4 * (1 + Real.log ((n:ℝ)+2))) := by
        apply mul_le_mul_of_nonneg_left h1logN
        positivity
    _ = (4 / (2 * c₀ * Real.pi))
          * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2))) := by ring

#print axioms perSpike_term1_le
#print axioms perSpike_term2_le
#print axioms perSpike_term3_le

#print axioms denseFctrRate_pos
#print axioms exp_half_admR_eq_rpow_quarter
#print axioms weight_integral_eq
#print axioms weight_integral_le

end

end RHFormalization
