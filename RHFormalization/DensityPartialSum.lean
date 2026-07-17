import Mathlib.Topology.Algebra.InfiniteSum.Real
import RHFormalization.ZetaZeroCounting

namespace RHFormalization

open Finset

/-- **Reduction of `hsum` to a uniform partial-sum bound.** If the partial sums of the zero-density
summand `mult(ρ)/(1+γ²)` over every finite set of nontrivial zeros are bounded by a single constant
`C`, then the density is summable. This routes the entire summability question through the
counting bound: any finite set of zeros lies in a disk, and the count controls the partial sum.
Direct application of `summable_of_sum_le` (nonneg + bounded finite partial sums ⟹ summable). -/
theorem summable_density_of_partialSum_bdd
    (M : ZeroMultiplicityData) (C : ℝ)
    (hbd : ∀ S : Finset {ρ : ℂ // IsNontrivialZetaZero ρ},
      ∑ ρ ∈ S, zeroDensitySummand M ρ ≤ C) :
    Summable (zeroDensitySummand M) :=
  summable_of_sum_le (fun ρ => zeroDensitySummand_nonneg M ρ) hbd

#print axioms summable_density_of_partialSum_bdd

end RHFormalization
