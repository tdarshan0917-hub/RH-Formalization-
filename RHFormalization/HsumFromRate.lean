import RHFormalization.BandDensityWeight

namespace RHFormalization

open Finset

/-- **Master reduction: `hsum` from a summable multiplicity-count rate.** Suppose `rate : ℕ → ℝ`
is nonnegative, the band-`k` multiplicity sum over any finite set of nontrivial zeros is `≤ rate k`,
and the down-weighted series `∑ rate k / (1 + k²)` is summable. Then the zero-density is summable.

This reduces the entire remaining problem to a single analytic obligation: produce such a `rate`
(the count of zeros at height `~k`, weighted by multiplicity) with `∑ rate k / (1+k²) < ∞`. The
count comes from the Jensen/Nevanlinna zero-counting bound; the summability is the
Riemann–von Mangoldt convergence. -/
theorem hsum_of_count_rate
    (M : ZeroMultiplicityData)
    (rate : ℕ → ℝ) (hrate_nonneg : ∀ k, 0 ≤ rate k)
    (hrate_count : ∀ (S : Finset {ρ : ℂ // IsNontrivialZetaZero ρ}) (k : ℕ),
      ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k), (M.mult ρ.1 : ℝ) ≤ rate k)
    (hrate_sum : Summable (fun k => rate k / (1 + (k : ℝ) ^ 2))) :
    Summable (zeroDensitySummand M) := by
  -- bound k := rate k / (1 + k²) is the per-band density bound
  apply hsum_of_band_bound M (fun k => rate k / (1 + (k : ℝ) ^ 2))
  · -- nonneg
    intro k
    apply div_nonneg (hrate_nonneg k)
    positivity
  · -- summable
    exact hrate_sum
  · -- each band's density sum ≤ rate k / (1+k²)
    intro S k
    refine (band_density_le_count_div M S k).trans ?_
    apply div_le_div_of_nonneg_right (hrate_count S k)
    positivity

#print axioms hsum_of_count_rate

end RHFormalization
