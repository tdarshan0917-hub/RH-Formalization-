import RHFormalization.DBFFStarBoundSplit

/-!
# DBFFStarMainPartOffParabolaBound

ROUTE CARD
1. Target: off-parabola half of O3 / hstar.
2. Object: `starMainPart`, the main-term plus fixed-term component of `starObject`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright from denominator separation and `mainTermIntegral_eval`.
6. Manuscript: D.OP-BOUND / D.OP.2 / off-parabola O3.
7. Consumer: `DBFFStarOffParabolaBound`.

This file proves the algebraic main-term estimate:
if `Re sqrt(s+1/4) ≥ 1/2 + δ`, then

  ‖starMainPart n s‖ ≤ 3 / δ.

The Dirichlet partial-sum part is handled separately by the L-series summability
brick.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- Denominator separation off the parabola. -/
theorem star_denominator_norm_ge_of_off_parabola
    {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hoff : (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    δ ≤ ‖(1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖ := by
  have hre :
      (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))).re) ≤ -δ := by
    simp [Complex.sub_re]
    linarith
  have habs :
      δ ≤ |(((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))).re)| := by
    have hre0 :
        (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))).re) ≤ 0 := by
      linarith
    rw [abs_of_nonpos hre0]
    simp
    linarith
  exact le_trans habs (Complex.abs_re_le_norm _)

/-- Reciprocal denominator bound off the parabola. -/
theorem star_inv_denominator_norm_le_of_off_parabola
    {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hoff : (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ‖(1 : ℂ) / ((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ)))‖ ≤ δ⁻¹ := by
  have hden := star_denominator_norm_ge_of_off_parabola hδ hoff
  have hden_pos : 0 < ‖(1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖ :=
    lt_of_lt_of_le hδ hden
  rw [norm_div, norm_one]
  rw [div_le_iff₀ hden_pos]
  rw [inv_mul_eq_div, le_div_iff₀ hδ]
  simpa using hden

/-- The exponential in the truncated main term has norm at most one off the parabola. -/
theorem star_mainTerm_exp_norm_le_one
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {s : ℂ}
    (hoff : (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ‖Complex.exp
        (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
          ((admR n : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hR0 : 0 ≤ admR n := (admR_pos n).le
  have hre :
      ((((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
          ((admR n : ℝ) : ℂ)).re) ≤ 0 := by
    rw [Complex.mul_re]
    simp [Complex.sub_re, Complex.sub_im]
    have hleft : (1 / 2 : ℝ) - (Complex.sqrt (s + (1/4 : ℂ))).re ≤ -δ := by
      linarith
    nlinarith
  exact Real.exp_le_one_iff.mpr hre

/-- Main-term component of `starObject` is bounded off the parabola. -/
theorem starMainPart_norm_le_off_parabola
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω)
    (hoff : (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ‖starMainPart n s‖ ≤ 3 / δ := by
  have hinv :=
    star_inv_denominator_norm_le_of_off_parabola hδ (s := s) hoff
  have hexp :=
    star_mainTerm_exp_norm_le_one hδ n (s := s) hoff
  have hmain := mainTermIntegral_eval n hs
  unfold starMainPart
  rw [hmain]
  have hquot :
      ‖(Complex.exp
          (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
            ((admR n : ℝ) : ℂ)) - 1)
          / ((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ)))‖
        ≤ 2 / δ := by
    rw [norm_div]
    have hnum :
        ‖Complex.exp
          (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
            ((admR n : ℝ) : ℂ)) - 1‖ ≤ 2 := by
      calc
        ‖Complex.exp
          (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
            ((admR n : ℝ) : ℂ)) - 1‖
            ≤ ‖Complex.exp
              (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
                ((admR n : ℝ) : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hexp (by norm_num)
        _ = 2 := by norm_num
    have hden := star_denominator_norm_ge_of_off_parabola hδ (s := s) hoff
    have hden_pos :
        0 < ‖(1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖ :=
      lt_of_lt_of_le hδ hden
    have hdeninv :
        (‖(1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖)⁻¹ ≤ δ⁻¹ := by
      have htmp :=
        star_inv_denominator_norm_le_of_off_parabola hδ (s := s) hoff
      rw [norm_div, norm_one] at htmp
      simpa [one_div] using htmp
    calc
      ‖Complex.exp
          (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
            ((admR n : ℝ) : ℂ)) - 1‖ /
          ‖(1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖
          = ‖Complex.exp
          (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
            ((admR n : ℝ) : ℂ)) - 1‖ *
            (‖(1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖)⁻¹ := by
              rw [div_eq_mul_inv]
      _ ≤ 2 * δ⁻¹ := mul_le_mul hnum hdeninv (inv_nonneg.mpr hden_pos.le) (by norm_num)
      _ = 2 / δ := by rw [div_eq_mul_inv]
  calc
    ‖(Complex.exp
        (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
          ((admR n : ℝ) : ℂ)) - 1)
        / ((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ)))
        + 1 / ((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ)))‖
        ≤ ‖(Complex.exp
          (((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ))) *
            ((admR n : ℝ) : ℂ)) - 1)
            / ((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ)))‖
          + ‖(1 : ℂ) / ((1/2 : ℂ) - Complex.sqrt (s + (1/4 : ℂ)))‖ := norm_add_le _ _
    _ ≤ 2 / δ + δ⁻¹ := add_le_add hquot hinv
    _ = 3 / δ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

#print axioms star_denominator_norm_ge_of_off_parabola
#print axioms star_inv_denominator_norm_le_of_off_parabola
#print axioms star_mainTerm_exp_norm_le_one
#print axioms starMainPart_norm_le_off_parabola

end

end RHFormalization
