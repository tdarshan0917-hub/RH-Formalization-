import RHFormalization.DBFFStarMainPartOffParabolaBound

/-!
# DBFFStarDirichletMajorantTransfer

ROUTE CARD
1. Target: Dirichlet partial-sum half of off-parabola O3.
2. Object: `starDirichletPartial`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright: finite sum norm bound from a nonnegative summable majorant.
6. Manuscript: D.OP-BOUND / D.OP.2 / off-parabola O3.
7. Consumer: `DBFFStarDirichletOffParabolaBound`.

This file does not yet prove the cpow/vonMangoldt term majorant. It proves the
clean transfer: once a summable majorant `M` bounds each Dirichlet term, every
finite Dirichlet partial sum is bounded by `∑' M`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Finset ArithmeticFunction

open scoped BigOperators Topology

/-- A nonnegative summable majorant controls finite sums by its total mass. -/
theorem finite_sum_le_tsum_of_nonneg_summable
    (M : ℕ → ℝ)
    (hM0 : ∀ k : ℕ, 0 ≤ M k)
    (hMsumm : Summable M)
    (I : Finset ℕ) :
    ∑ k ∈ I, M k ≤ ∑' k : ℕ, M k := by
  exact hMsumm.sum_le_tsum I (fun k _ => hM0 k)

/--
If each Dirichlet term is bounded by a fixed nonnegative summable majorant `M`,
then the Dirichlet partial part is bounded by `∑' M`.
-/
theorem starDirichletPartial_norm_le_tsum_majorant
    (K : Set ℂ)
    (M : ℕ → ℝ)
    (hM0 : ∀ k : ℕ, 0 ≤ M k)
    (hMsumm : Summable M)
    (hterm :
      ∀ n : ℕ, ∀ s ∈ K,
        ∀ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
          ‖LSeries.term
              (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)) k‖ ≤ M k) :
    ∀ n : ℕ, ∀ s ∈ K,
      ‖starDirichletPartial n s‖ ≤ ∑' k : ℕ, M k := by
  intro n s hs
  unfold starDirichletPartial
  calc
    ‖∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
        LSeries.term
          (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)) k‖
        ≤ ∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
            ‖LSeries.term
              (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)) k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊, M k := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm n s hs k hk
    _ ≤ ∑' k : ℕ, M k :=
          finite_sum_le_tsum_of_nonneg_summable M hM0 hMsumm _

/--
Uniform boundedness form for `starDirichletPartial` from a summable majorant.

This is the exact bridge consumed by the off-parabola star bound once the
specific von Mangoldt majorant is supplied.
-/
theorem starDirichletPartial_bounded_of_majorant
    (K : Set ℂ)
    (M : ℕ → ℝ)
    (hM0 : ∀ k : ℕ, 0 ≤ M k)
    (hMsumm : Summable M)
    (hterm :
      ∀ n : ℕ, ∀ s ∈ K,
        ∀ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
          ‖LSeries.term
              (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (Complex.sqrt (s + (1/4 : ℂ)) + (1/2 : ℂ)) k‖ ≤ M k) :
    ∃ Cdir : ℝ,
      ∀ n : ℕ, ∀ s ∈ K, ‖starDirichletPartial n s‖ ≤ Cdir := by
  refine ⟨∑' k : ℕ, M k, ?_⟩
  exact starDirichletPartial_norm_le_tsum_majorant K M hM0 hMsumm hterm

#print axioms finite_sum_le_tsum_of_nonneg_summable
#print axioms starDirichletPartial_norm_le_tsum_majorant
#print axioms starDirichletPartial_bounded_of_majorant

end

end RHFormalization
