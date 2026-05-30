import RHFormalization.CanonicalPrimePowerCountWeightQuotient

/-!
# RHFormalization.CanonicalPrimePowerCountWeightProductBound

Bare product-bound theorem for the remaining count/weight quotient estimate.

This file is intentionally not another package frontier.

It proves the concrete estimate mechanism needed for

  (countEnvelope R_n * weightEnvelope R_n) / denominatorBound n → 0.

The new decomposition is:

* countEnvelope(R_n) ≤ countBound n;
* weightEnvelope(R_n) ≤ weightBound n;
* countBound n * weightBound n ≤ numeratorBound n;
* numeratorBound n / denominatorBound n → 0.

This separates prime-power counting, weight normalization, and denominator-speed
domination.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If `countEnvelope ≤ countBound` and `weightEnvelope ≤ weightBound`, then the
count/weight product is bounded by `countBound * weightBound`.
-/
theorem countWeight_product_le_of_factor_bounds
    (countEnvelope weightEnvelope countBound weightBound : ℕ → ℝ)
    (h_countEnvelope_le_countBound :
      ∀ n : ℕ, countEnvelope n ≤ countBound n)
    (h_weightEnvelope_le_weightBound :
      ∀ n : ℕ, weightEnvelope n ≤ weightBound n)
    (h_weightEnvelope_nonneg :
      ∀ n : ℕ, 0 ≤ weightEnvelope n)
    (h_countBound_nonneg :
      ∀ n : ℕ, 0 ≤ countBound n) :
    ∀ n : ℕ,
      countEnvelope n * weightEnvelope n ≤
        countBound n * weightBound n := by
  intro n
  exact
    mul_le_mul
      (h_countEnvelope_le_countBound n)
      (h_weightEnvelope_le_weightBound n)
      (h_weightEnvelope_nonneg n)
      (h_countBound_nonneg n)

/--
If the count and weight envelopes are separately bounded and the resulting
numerator divided by the denominator tends to zero, then the original
count/weight quotient tends to zero.
-/
theorem countWeight_div_denominator_tendsto_zero_of_factor_bounds
    (countEnvelope weightEnvelope countBound weightBound denominatorBound numeratorBound : ℕ → ℝ)
    (h_countEnvelope_nonneg :
      ∀ n : ℕ, 0 ≤ countEnvelope n)
    (h_weightEnvelope_nonneg :
      ∀ n : ℕ, 0 ≤ weightEnvelope n)
    (h_countBound_nonneg :
      ∀ n : ℕ, 0 ≤ countBound n)
    (h_denominatorBound_pos :
      ∀ n : ℕ, 0 < denominatorBound n)
    (h_numeratorBound_nonneg :
      ∀ n : ℕ, 0 ≤ numeratorBound n)
    (h_countEnvelope_le_countBound :
      ∀ n : ℕ, countEnvelope n ≤ countBound n)
    (h_weightEnvelope_le_weightBound :
      ∀ n : ℕ, weightEnvelope n ≤ weightBound n)
    (h_countWeightBound_le_numerator :
      ∀ n : ℕ,
        countBound n * weightBound n ≤ numeratorBound n)
    (h_numerator_div_denominator_tendsto_zero :
      Tendsto
        (fun n : ℕ => numeratorBound n / denominatorBound n)
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (countEnvelope n * weightEnvelope n) / denominatorBound n)
      Filter.atTop
      (𝓝 0) := by
  have h_product_le_bound :
      ∀ n : ℕ,
        countEnvelope n * weightEnvelope n ≤
          countBound n * weightBound n :=
    countWeight_product_le_of_factor_bounds
      countEnvelope
      weightEnvelope
      countBound
      weightBound
      h_countEnvelope_le_countBound
      h_weightEnvelope_le_weightBound
      h_weightEnvelope_nonneg
      h_countBound_nonneg

  have h_countWeight_le_numerator :
      ∀ n : ℕ,
        countEnvelope n * weightEnvelope n ≤ numeratorBound n := by
    intro n
    exact le_trans
      (h_product_le_bound n)
      (h_countWeightBound_le_numerator n)

  exact
    countWeight_div_denominator_tendsto_zero_of_numerator_bound
      countEnvelope
      weightEnvelope
      denominatorBound
      numeratorBound
      h_countEnvelope_nonneg
      h_weightEnvelope_nonneg
      h_denominatorBound_pos
      h_numeratorBound_nonneg
      h_countWeight_le_numerator
      h_numerator_div_denominator_tendsto_zero

/--
Cutoff-sequence version of the factor-bound quotient theorem.

This is the exact shape used by the current prime-power mass frontier, where
the envelopes are functions of the cutoff `R_n`.
-/
theorem countWeight_div_denominator_tendsto_zero_of_cutoff_factor_bounds
    (Rseq : ℕ → ℝ)
    (countEnvelope weightEnvelope : ℝ → ℝ)
    (countBound weightBound denominatorBound numeratorBound : ℕ → ℝ)
    (h_countEnvelope_nonneg :
      ∀ R : ℝ, 0 ≤ countEnvelope R)
    (h_weightEnvelope_nonneg :
      ∀ R : ℝ, 0 ≤ weightEnvelope R)
    (h_countBound_nonneg :
      ∀ n : ℕ, 0 ≤ countBound n)
    (h_denominatorBound_pos :
      ∀ n : ℕ, 0 < denominatorBound n)
    (h_numeratorBound_nonneg :
      ∀ n : ℕ, 0 ≤ numeratorBound n)
    (h_countEnvelope_le_countBound :
      ∀ n : ℕ,
        countEnvelope (Rseq n) ≤ countBound n)
    (h_weightEnvelope_le_weightBound :
      ∀ n : ℕ,
        weightEnvelope (Rseq n) ≤ weightBound n)
    (h_countWeightBound_le_numerator :
      ∀ n : ℕ,
        countBound n * weightBound n ≤ numeratorBound n)
    (h_numerator_div_denominator_tendsto_zero :
      Tendsto
        (fun n : ℕ => numeratorBound n / denominatorBound n)
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (countEnvelope (Rseq n) * weightEnvelope (Rseq n)) /
          denominatorBound n)
      Filter.atTop
      (𝓝 0) := by
  exact
    countWeight_div_denominator_tendsto_zero_of_factor_bounds
      (fun n : ℕ => countEnvelope (Rseq n))
      (fun n : ℕ => weightEnvelope (Rseq n))
      countBound
      weightBound
      denominatorBound
      numeratorBound
      (fun n => h_countEnvelope_nonneg (Rseq n))
      (fun n => h_weightEnvelope_nonneg (Rseq n))
      h_countBound_nonneg
      h_denominatorBound_pos
      h_numeratorBound_nonneg
      h_countEnvelope_le_countBound
      h_weightEnvelope_le_weightBound
      h_countWeightBound_le_numerator
      h_numerator_div_denominator_tendsto_zero

end

end RHFormalization
