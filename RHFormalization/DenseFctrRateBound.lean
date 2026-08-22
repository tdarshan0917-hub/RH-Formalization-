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


/-! ## Installment 2b: the compact rate theorem

Chain: ‖denseFctr n s‖ ≤ ∫‖·‖ (norm_integral_le_integral_norm)
  ≤ ∫ e^{u/2}·[2·perSpikeBound + (admR/L)c₁⁻¹]   (part-1 majorant, u ≤ admR)
  = M · ∫ e^{u/2} ≤ M · 2x^{1/4}                  (weight_integral_le)
with M ≤ A·x^{-3/8}(1+log x) + B·x^{-1} from the three term lemmas
+ admR/L ≤ x^{-3/8}(1+log x), then x^{1/4}·x^{-3/8} = x^{-1/8},
x^{1/4}·x^{-1} = x^{-3/4} (Real.rpow_add). -/

/-- The three term lemmas summed against `perSpikeBound` at the dense schedule. -/
theorem perSpikeBound_dense_le (n : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    perSpikeBound (admR n) (denseL n) (denseN n) c₀
      ≤ (Real.pi / (4 * c₀) + 1 / c₀^2 + 4 / (2 * c₀ * Real.pi))
          * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)))
        + (1 / (2 * c₀ * Real.pi^2)) * (((n:ℝ)+2) ^ (-(1:ℝ))) := by
  have h1 := perSpike_term1_le n hc₀
  have h2 := perSpike_term2_le n hc₀
  have h3 := perSpike_term3_le n hc₀
  unfold perSpikeBound
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  ring

/-- Centering ratio: `admR n / denseL n ≤ x^{-3/8}(1+log x)` via the L floor. -/
theorem admR_div_denseL_le (n : ℕ) :
    admR n / denseL n
      ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)) := by
  have hx : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hlog : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith)
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have hr : (0:ℝ) < ((n:ℝ)+2) ^ ((3:ℝ)/8) := Real.rpow_pos_of_pos hx _
  have hneg : ((n:ℝ)+2) ^ (-(3:ℝ)/8) = (((n:ℝ)+2) ^ ((3:ℝ)/8))⁻¹ := by
    rw [neg_div, Real.rpow_neg hx.le]
  have hinv : (denseL n)⁻¹ ≤ (((n:ℝ)+2) ^ ((3:ℝ)/8))⁻¹ :=
    inv_anti₀ hr (rpow_le_denseL n)
  have hR : admR n ≤ 1 + Real.log ((n:ℝ)+2) := by
    unfold admR; linarith
  rw [hneg, div_eq_mul_inv]
  calc admR n * (denseL n)⁻¹
      ≤ (1 + Real.log ((n:ℝ)+2)) * (((n:ℝ)+2) ^ ((3:ℝ)/8))⁻¹ :=
        mul_le_mul hR hinv (inv_nonneg.mpr hL0.le) (by linarith)
    _ = _ := mul_comm _ _

/-- Integral majorant: pull the part-1 pointwise bound (with `u ≤ admR n`)
through the interval integral against the weight `e^{u/2}`. -/
theorem denseFctr_norm_le_majorant
    (n : ℕ) {K : Set ℂ} (hKΩ : K ⊆ Ω)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hfl : ∀ s ∈ K, ∀ ξ : ℝ, c₀ * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hc₁K : ∀ s ∈ K, c₁ ≤ ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖)
    {s : ℂ} (hs : s ∈ K) :
    ‖denseFctr n s‖
      ≤ (2 * perSpikeBound (admR n) (denseL n) (denseN n) c₀
            + (admR n / denseL n) * c₁⁻¹)
          * ∫ u in (0:ℝ)..(admR n), Real.exp (u/2) := by
  have hR0 : (0:ℝ) ≤ admR n := (admR_pos n).le
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  unfold denseFctr
  refine (intervalIntegral.norm_integral_le_integral_norm hR0).trans ?_
  have hpt : ∀ u ∈ Set.Icc (0:ℝ) (admR n),
      ‖((Real.exp (u/2) : ℝ) : ℂ)
          * (denseKernelN n u s - shiftedLaplaceHeatKernelC u s)‖
        ≤ Real.exp (u/2)
            * (2 * perSpikeBound (admR n) (denseL n) (denseN n) c₀
                + (admR n / denseL n) * c₁⁻¹) := by
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    refine (denseKernelN_sub_kernel_norm_le n hKΩ hc₀ hfl hc₁ hc₁K hs hu.1 hu.2).trans ?_
    have : u / denseL n * c₁⁻¹ ≤ admR n / denseL n * c₁⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hc₁.le)
      exact div_le_div_of_nonneg_right hu.2 hL0.le
    linarith
  have hint :
      ∫ u in (0:ℝ)..(admR n),
          ‖((Real.exp (u/2) : ℝ) : ℂ)
            * (denseKernelN n u s - shiftedLaplaceHeatKernelC u s)‖
        ≤ ∫ u in (0:ℝ)..(admR n),
            Real.exp (u/2)
              * (2 * perSpikeBound (admR n) (denseL n) (denseN n) c₀
                  + (admR n / denseL n) * c₁⁻¹) := by
    apply intervalIntegral.integral_mono_on hR0
    · exact (denseFctr_integrand_intervalIntegrable n s).norm
    · exact (by fun_prop : Continuous fun u : ℝ => Real.exp (u/2)
          * (2 * perSpikeBound (admR n) (denseL n) (denseN n) c₀
              + (admR n / denseL n) * c₁⁻¹)).intervalIntegrable _ _
    · exact hpt
  rw [intervalIntegral.integral_mul_const] at hint
  calc _ ≤ _ := hint
    _ = _ := mul_comm _ _

/-- **B(i)-6 compact rate theorem.** On every compact `K ⊆ Ω` there is
`C_K > 0` with `‖denseFctr n s‖ ≤ C_K · denseFctrRate n` for all `n`, `s ∈ K`. -/
theorem denseFctr_norm_le_rate (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ K, ‖denseFctr n s‖ ≤ C * denseFctrRate n := by
  obtain ⟨c₀, hc₀, hfl⟩ := resolventDenom_lower_bound K hK hKΩ
  obtain ⟨c₁, hc₁, hc₁K⟩ := kernelDenom_min K hK hKΩ
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = 2 * (Real.pi / (4 * c₀) + 1 / c₀^2 + 4 / (2 * c₀ * Real.pi)) + c₁⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * (1 / (2 * c₀ * Real.pi^2)) := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; positivity
  have hB : 0 < B := by rw [hBdef]; positivity
  refine ⟨2 * A + 2 * B, by positivity, ?_⟩
  intro n s hs
  have hx : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hlog : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith)
  have hT0 : 0 ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)) :=
    mul_nonneg (Real.rpow_nonneg hx.le _) (by linarith)
  have hU0 : 0 ≤ ((n:ℝ)+2) ^ (-(1:ℝ)) := Real.rpow_nonneg hx.le _
  have hM : 2 * perSpikeBound (admR n) (denseL n) (denseN n) c₀
        + (admR n / denseL n) * c₁⁻¹
      ≤ A * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)))
        + B * (((n:ℝ)+2) ^ (-(1:ℝ))) := by
    have h1 := perSpikeBound_dense_le n hc₀
    have h2 : (admR n / denseL n) * c₁⁻¹
        ≤ (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2))) * c₁⁻¹ :=
      mul_le_mul_of_nonneg_right (admR_div_denseL_le n) (inv_nonneg.mpr hc₁.le)
    rw [hAdef, hBdef]
    linarith
  have hW := weight_integral_le n
  have hW0 : 0 ≤ ∫ u in (0:ℝ)..(admR n), Real.exp (u/2) :=
    intervalIntegral.integral_nonneg (admR_pos n).le (fun u _ => (Real.exp_pos _).le)
  have hAT : 0 ≤ A * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)))
        + B * (((n:ℝ)+2) ^ (-(1:ℝ))) :=
    add_nonneg (mul_nonneg hA.le hT0) (mul_nonneg hB.le hU0)
  have step1 : ‖denseFctr n s‖
      ≤ (A * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)))
          + B * (((n:ℝ)+2) ^ (-(1:ℝ))))
        * (2 * ((n:ℝ)+2) ^ ((1:ℝ)/4)) := by
    calc ‖denseFctr n s‖
        ≤ _ := denseFctr_norm_le_majorant n hKΩ hc₀ hfl hc₁ hc₁K hs
      _ ≤ _ := mul_le_mul_of_nonneg_right hM hW0
      _ ≤ _ := mul_le_mul_of_nonneg_left hW hAT
  have e1 : ((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2) ^ (-(3:ℝ)/8)
      = ((n:ℝ)+2) ^ (-(1:ℝ)/8) := by
    rw [← Real.rpow_add hx]; norm_num
  have e2 : ((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2) ^ (-(1:ℝ))
      = ((n:ℝ)+2) ^ (-(3:ℝ)/4) := by
    rw [← Real.rpow_add hx]; norm_num
  have key : (A * (((n:ℝ)+2) ^ (-(3:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)))
          + B * (((n:ℝ)+2) ^ (-(1:ℝ))))
        * (2 * ((n:ℝ)+2) ^ ((1:ℝ)/4))
      = 2 * A * (((n:ℝ)+2) ^ (-(1:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)))
        + 2 * B * ((n:ℝ)+2) ^ (-(3:ℝ)/4) := by
    rw [← e1, ← e2]; ring
  have hr1 : 0 ≤ ((n:ℝ)+2) ^ (-(1:ℝ)/8) * (1 + Real.log ((n:ℝ)+2)) :=
    mul_nonneg (Real.rpow_nonneg hx.le _) (by linarith)
  have hr2 : 0 ≤ ((n:ℝ)+2) ^ (-(3:ℝ)/4) := Real.rpow_nonneg hx.le _
  unfold denseFctrRate
  calc ‖denseFctr n s‖ ≤ _ := step1
    _ = _ := key
    _ ≤ (2 * A + 2 * B)
          * (((n:ℝ)+2) ^ (-(1:ℝ)/8) * (1 + Real.log ((n:ℝ)+2))
              + ((n:ℝ)+2) ^ (-(3:ℝ)/4)) := by
        nlinarith [mul_nonneg hA.le hr2, mul_nonneg hB.le hr1]


/-! ## Installment 2c: rate → 0 and the rate-free compact-uniform corollary -/

/-- `x^{-1/8}·log x → 0` at `+∞`, from `log = o(x^{1/8})`. -/
theorem rpow_neg_eighth_mul_log_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => x ^ (-(1:ℝ)/8) * Real.log x)
      Filter.atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
  rw [neg_div, Real.rpow_neg hx, div_eq_mul_inv, mul_comm]

/-- The continuous-variable rate tends to zero. -/
theorem rateFun_tendsto_zero :
    Filter.Tendsto
      (fun x : ℝ => x ^ (-(1:ℝ)/8) * (1 + Real.log x) + x ^ (-(3:ℝ)/4))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => x ^ (-(1:ℝ)/8)) Filter.atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := (1:ℝ)/8) (by norm_num)
    simpa [neg_div] using this
  have h2 : Filter.Tendsto (fun x : ℝ => x ^ (-(3:ℝ)/4)) Filter.atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := (3:ℝ)/4) (by norm_num)
    simpa [neg_div] using this
  have h3 := rpow_neg_eighth_mul_log_tendsto_zero
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-(1:ℝ)/8) * (1 + Real.log x))
      Filter.atTop (nhds (0 + 0)) :=
    (h0.add h3).congr (fun x => by ring)
  have := h1.add h2
  simpa using this

/-- **B6 rate decay.** `denseFctrRate n → 0`. -/
theorem denseFctrRate_tendsto_zero :
    Filter.Tendsto denseFctrRate Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have heq : denseFctrRate
      = (fun x : ℝ => x ^ (-(1:ℝ)/8) * (1 + Real.log x) + x ^ (-(3:ℝ)/4))
          ∘ (fun n : ℕ => (n : ℝ) + 2) := by
    funext n; rfl
  rw [heq]
  exact rateFun_tendsto_zero.comp hg

/-- **B6 rate-free corollary.** `denseFctr` is uniformly bounded on every
compact `K ⊆ Ω`, uniformly in `n`. -/
theorem denseFctr_bounded_on_compact (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ M : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖denseFctr n s‖ ≤ M := by
  obtain ⟨C, hC, hrate⟩ := denseFctr_norm_le_rate K hK hKΩ
  obtain ⟨R, hR⟩ := denseFctrRate_tendsto_zero.bddAbove_range
  refine ⟨C * R, fun n s hs => ?_⟩
  have hn : denseFctrRate n ≤ R := hR ⟨n, rfl⟩
  calc ‖denseFctr n s‖ ≤ C * denseFctrRate n := hrate n s hs
    _ ≤ C * R := mul_le_mul_of_nonneg_left hn hC.le

#print axioms perSpike_term1_le
#print axioms perSpike_term2_le
#print axioms perSpike_term3_le

#print axioms denseFctrRate_pos
#print axioms exp_half_admR_eq_rpow_quarter
#print axioms weight_integral_eq
#print axioms weight_integral_le

#print axioms perSpikeBound_dense_le
#print axioms admR_div_denseL_le
#print axioms denseFctr_norm_le_majorant
#print axioms denseFctr_norm_le_rate

#print axioms rpow_neg_eighth_mul_log_tendsto_zero
#print axioms rateFun_tendsto_zero
#print axioms denseFctrRate_tendsto_zero
#print axioms denseFctr_bounded_on_compact

end

end RHFormalization
