import RHFormalization.CanonicalPrimePowerSoundCutoffCounting

/-!
# RHFormalization.CanonicalPrimePowerCountWeightQuotient

Bare quotient theorem for the remaining count/weight over D-window-speed estimate.

This file is intentionally not a new package frontier.

It proves the direct analytic-comparison lemma needed for the remaining field

  h_countWeight_div_denominator_tendsto_zero :
    (countEnvelope R_n * weightEnvelope R_n) / denominatorBound s n → 0.

The point is to stop adding wrappers and prove the actual quotient comparison
step.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the concrete count/weight numerator is bounded by `numeratorBound`, and
`numeratorBound / denominatorBound → 0`, then the original count/weight quotient
also tends to zero.

This is the bare theorem needed for the mass-side frontier.
-/
theorem countWeight_div_denominator_tendsto_zero_of_numerator_bound
    (countEnvelope weightEnvelope denominatorBound numeratorBound : ℕ → ℝ)
    (h_countEnvelope_nonneg :
      ∀ n : ℕ, 0 ≤ countEnvelope n)
    (h_weightEnvelope_nonneg :
      ∀ n : ℕ, 0 ≤ weightEnvelope n)
    (h_denominatorBound_pos :
      ∀ n : ℕ, 0 < denominatorBound n)
    (h_numeratorBound_nonneg :
      ∀ n : ℕ, 0 ≤ numeratorBound n)
    (h_countWeight_le_numerator :
      ∀ n : ℕ,
        countEnvelope n * weightEnvelope n ≤ numeratorBound n)
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
  exact
    real_tendsto_zero_of_nonneg_bound
      (u := fun n : ℕ =>
        (countEnvelope n * weightEnvelope n) / denominatorBound n)
      (b := fun n : ℕ =>
        numeratorBound n / denominatorBound n)
      (by
        intro n
        exact
          div_nonneg
            (mul_nonneg
              (h_countEnvelope_nonneg n)
              (h_weightEnvelope_nonneg n))
            (le_of_lt (h_denominatorBound_pos n)))
      (by
        intro n
        exact
          div_le_div_of_nonneg_right
            (h_countWeight_le_numerator n)
            (le_of_lt (h_denominatorBound_pos n)))
      (by
        intro n
        exact
          div_nonneg
            (h_numeratorBound_nonneg n)
            (le_of_lt (h_denominatorBound_pos n)))
      h_numerator_div_denominator_tendsto_zero

/--
Specialized version along a cutoff sequence `R_n`.

This is exactly the shape needed by the current D-side mass-counting frontier.
-/
theorem countWeight_div_denominator_tendsto_zero_of_cutoff_numerator_bound
    (Rseq : ℕ → ℝ)
    (countEnvelope weightEnvelope : ℝ → ℝ)
    (denominatorBound numeratorBound : ℕ → ℝ)
    (h_countEnvelope_nonneg :
      ∀ R : ℝ, 0 ≤ countEnvelope R)
    (h_weightEnvelope_nonneg :
      ∀ R : ℝ, 0 ≤ weightEnvelope R)
    (h_denominatorBound_pos :
      ∀ n : ℕ, 0 < denominatorBound n)
    (h_numeratorBound_nonneg :
      ∀ n : ℕ, 0 ≤ numeratorBound n)
    (h_countWeight_le_numerator :
      ∀ n : ℕ,
        countEnvelope (Rseq n) * weightEnvelope (Rseq n) ≤
          numeratorBound n)
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
    countWeight_div_denominator_tendsto_zero_of_numerator_bound
      (fun n : ℕ => countEnvelope (Rseq n))
      (fun n : ℕ => weightEnvelope (Rseq n))
      denominatorBound
      numeratorBound
      (fun n => h_countEnvelope_nonneg (Rseq n))
      (fun n => h_weightEnvelope_nonneg (Rseq n))
      h_denominatorBound_pos
      h_numeratorBound_nonneg
      h_countWeight_le_numerator
      h_numerator_div_denominator_tendsto_zero

end

end RHFormalization
