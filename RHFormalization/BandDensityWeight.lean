import RHFormalization.DensityBandBound

namespace RHFormalization

open Finset

/-- **Within a height band, the density sum is the multiplicity sum down-weighted by `1/(1+k²)`.**
For a nontrivial zero `ρ` in band `k` (i.e. `⌊|im ρ|⌋₊ = k`), the imaginary part satisfies
`k ≤ |im ρ|`, hence `1 + k² ≤ 1 + (im ρ)²`, so `mult(ρ)/(1+(im ρ)²) ≤ mult(ρ)/(1+k²)`. Summing,
the band-`k` density sum is bounded by `(∑ mult)/(1+k²)`. -/
theorem band_density_le_count_div
    (M : ZeroMultiplicityData)
    (S : Finset {ρ : ℂ // IsNontrivialZetaZero ρ}) (k : ℕ) :
    ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k), zeroDensitySummand M ρ
      ≤ (∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k), (M.mult ρ.1 : ℝ)) / (1 + (k : ℝ) ^ 2) := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ρ hρ
  -- ρ is in band k: ⌊|im ρ|⌋₊ = k, so (k:ℝ) ≤ |im ρ|
  rw [Finset.mem_filter] at hρ
  have hk_le : (k : ℝ) ≤ |ρ.1.im| := by
    rw [← hρ.2]; exact Nat.floor_le (abs_nonneg _)
  -- 1 + k² ≤ 1 + (im ρ)²
  have hdenom : 1 + (k : ℝ) ^ 2 ≤ 1 + ρ.1.im ^ 2 := by
    have habs : (k : ℝ) ^ 2 ≤ ρ.1.im ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (Nat.cast_nonneg k)]
      exact hk_le
    linarith
  -- so mult/(1+im²) ≤ mult/(1+k²)
  unfold zeroDensitySummand
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hdenom

#print axioms band_density_le_count_div

end RHFormalization
