import RHFormalization.DBFFStarDirichletMajorantTransfer
import RHFormalization.PrimePowerSumConvergence

/-!
# DBFFStarDirichletOffParabolaBound

ROUTE CARD
1. Target: Dirichlet partial-sum half of off-parabola O3 / `hstar`.
2. Object: `starDirichletPartial`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright from `vonMangoldt_LSeriesSummable` and cpow norm monotonicity.
6. Manuscript: D.OP-BOUND / D.OP.2 / off-parabola O3.
7. Consumer: `DBFFStarOffParabolaBound`.

This file proves: if `Re sqrt(s+1/4) ≥ 1/2 + δ`, then the Dirichlet
partial part of `starObject` is uniformly bounded by the absolutely summable
von Mangoldt L-series at exponent `1 + δ`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Finset ArithmeticFunction

open scoped BigOperators Topology

/-- The fixed off-parabola von Mangoldt majorant at exponent `1 + δ`. -/
noncomputable def offParaMajorant (δ : ℝ) (k : ℕ) : ℝ :=
  ‖LSeries.term
      (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (((1 : ℝ) + δ : ℝ) : ℂ) k‖

/-- The off-parabola majorant is nonnegative. -/
theorem offParaMajorant_nonneg (δ : ℝ) (k : ℕ) :
    0 ≤ offParaMajorant δ k := by
  unfold offParaMajorant
  exact norm_nonneg _

/-- The off-parabola majorant is summable for `δ > 0`. -/
theorem offParaMajorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (offParaMajorant δ) := by
  unfold offParaMajorant
  have hs : 1 < ((((1 : ℝ) + δ : ℝ) : ℂ).re) := by
    simp
    linarith
  have hsum :
      Summable
        (LSeries.term
          (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (((1 : ℝ) + δ : ℝ) : ℂ)) :=
    vonMangoldt_LSeriesSummable hs
  exact (summable_norm_iff).2 hsum

/--
Termwise off-parabola domination: if
`1/2 + δ ≤ Re sqrt(s+1/4)`, then the von Mangoldt term at
`sqrt(s+1/4)+1/2` is bounded by the fixed term at exponent `1+δ`.
-/
theorem vonMangoldt_term_norm_le_offParaMajorant
    {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hoff : (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re)
    (k : ℕ) :
    ‖LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)) k‖
      ≤ offParaMajorant δ k := by
  unfold offParaMajorant
  by_cases hk : k = 0
  · subst k
    simp [LSeries.term]
  · have hkposR : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hkoneR : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hΛnonneg : 0 ≤ ArithmeticFunction.vonMangoldt k :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hΛnorm :
        ‖(ArithmeticFunction.vonMangoldt k : ℂ)‖ =
          ArithmeticFunction.vonMangoldt k := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛnonneg]

    rw [vonMangoldt_term_eq (s := Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)) hk]
    rw [vonMangoldt_term_eq (s := (((1 : ℝ) + δ : ℝ) : ℂ)) hk]
    rw [norm_div, norm_div]
    repeat rw [hΛnorm]

    have hnorm_z :
        ‖(k : ℂ) ^ (Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ))‖ =
          (k : ℝ) ^ ((Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)).re) := by
      simpa using
        (Complex.norm_cpow_eq_rpow_re_of_pos
          (x := (k : ℝ))
          hkposR
          (y := Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)))

    have hnorm_delta :
        ‖(k : ℂ) ^ ((((1 : ℝ) + δ : ℝ) : ℂ))‖ =
          (k : ℝ) ^ (((((1 : ℝ) + δ : ℝ) : ℂ)).re) := by
      simpa using
        (Complex.norm_cpow_eq_rpow_re_of_pos
          (x := (k : ℝ))
          hkposR
          (y := ((((1 : ℝ) + δ : ℝ) : ℂ))))

    rw [hnorm_z, hnorm_delta]

    have hzre :
        (((1 : ℝ) + δ : ℝ) : ℂ).re
          ≤ (Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)).re := by
      simp [Complex.add_re]
      linarith

    have hden_le :
        (k : ℝ) ^ ((((1 : ℝ) + δ : ℝ) : ℂ).re)
          ≤ (k : ℝ) ^ ((Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)).re) := by
      exact Real.rpow_le_rpow_of_exponent_le hkoneR hzre

    have hden_pos_z :
        0 < (k : ℝ) ^ ((Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)).re) :=
      Real.rpow_pos_of_pos hkposR _
    have hden_pos_δ :
        0 < (k : ℝ) ^ ((((1 : ℝ) + δ : ℝ) : ℂ).re) :=
      Real.rpow_pos_of_pos hkposR _

    -- Bigger exponent gives larger denominator; with nonnegative numerator,
    -- the quotient is smaller.
    rw [div_le_div_iff₀ hden_pos_z hden_pos_δ]
    exact mul_le_mul_of_nonneg_left hden_le hΛnonneg

/-- The Dirichlet partial part is uniformly bounded off the parabola. -/
theorem starDirichletPartial_bounded_off_parabola
    (K : Set ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hoff : ∀ s ∈ K,
      (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ∃ Cdir : ℝ,
      ∀ n : ℕ, ∀ s ∈ K, ‖starDirichletPartial n s‖ ≤ Cdir := by
  refine starDirichletPartial_bounded_of_majorant
    K
    (offParaMajorant δ)
    (offParaMajorant_nonneg δ)
    (offParaMajorant_summable hδ)
    ?_
  intro n s hs k hk
  exact vonMangoldt_term_norm_le_offParaMajorant hδ (hoff s hs) k

#print axioms offParaMajorant
#print axioms offParaMajorant_nonneg
#print axioms offParaMajorant_summable
#print axioms vonMangoldt_term_norm_le_offParaMajorant
#print axioms starDirichletPartial_bounded_off_parabola

end

end RHFormalization
