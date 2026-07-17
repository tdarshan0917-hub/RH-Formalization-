import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.PSeries
import RHFormalization.DensityPartialSum

namespace RHFormalization

open Finset

/-- **Height-band reduction of `hsum`.** Index each nontrivial zero `ρ` by its height-band
`k = ⌊|im ρ|⌋₊`. If there is a summable nonnegative sequence `bound : ℕ → ℝ` such that, for every
finite set `S` of nontrivial zeros, the partial sum of the density summand restricted to band `k`
is `≤ bound k`, then the full density is summable.

This packages the dyadic/banding plumbing: the entire remaining analytic content is producing
such a `bound` from the zero-counting estimate. -/
theorem hsum_of_band_bound
    (M : ZeroMultiplicityData)
    (bound : ℕ → ℝ) (hbound_nonneg : ∀ k, 0 ≤ bound k) (hbound_sum : Summable bound)
    (hband : ∀ (S : Finset {ρ : ℂ // IsNontrivialZetaZero ρ}) (k : ℕ),
      ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k), zeroDensitySummand M ρ ≤ bound k) :
    Summable (zeroDensitySummand M) := by
  set C : ℝ := ∑' k, bound k with hC
  apply summable_density_of_partialSum_bdd M C
  intro S
  -- partition S by band index ⌊|im|⌋₊, bound each band by `bound k`, sum ≤ ∑' bound
  classical
  -- the band indices occurring in S
  set K : Finset ℕ := S.image (fun ρ => ⌊|ρ.1.im|⌋₊) with hK
  -- partition the sum over S into a sum over bands
  have hpart : ∑ ρ ∈ S, zeroDensitySummand M ρ
      = ∑ k ∈ K, ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k), zeroDensitySummand M ρ := by
    rw [hK]
    exact (Finset.sum_fiberwise_of_maps_to (fun ρ hρ => Finset.mem_image_of_mem _ hρ) _).symm
  rw [hpart]
  -- each band ≤ bound k
  have hbandle : ∑ k ∈ K, ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k), zeroDensitySummand M ρ
      ≤ ∑ k ∈ K, bound k :=
    Finset.sum_le_sum (fun k _ => hband S k)
  refine hbandle.trans ?_
  -- ∑_{k ∈ K} bound k ≤ ∑' k, bound k  (nonneg summable)
  rw [hC]
  exact sum_le_hasSum K (fun k _ => hbound_nonneg k) hbound_sum.hasSum

#print axioms hsum_of_band_bound

end RHFormalization
