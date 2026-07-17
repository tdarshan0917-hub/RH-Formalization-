import RHFormalization.HsumFromRate
import RHFormalization.NevanlinnaBound

namespace RHFormalization

open Finset ValueDistribution

/-- **CAPSTONE (route skeleton): `hsum` from a multiplicity-count-rate hypothesis.**

This re-exports the master reduction `hsum_of_count_rate` under the name that documents the
remaining obligation. The full route is:

  Λ₀ growth bound (G1-G3, MellinBound + GrowthEngine)
    ⟹ `N(r) = logCounting Λ₀ 0 r ≤ log⁺ M(r) + C` (brick 28, NevanlinnaBound)  [M(r) ≤ G(r)/2]
    ⟹ `N(r) = O(r log r)`
    ⟹ raw zero-count `n(R) = ∑_{‖ρ‖≤R} mult(ρ) = O(R log R)` (logCounting finsum + monotonicity)
    ⟹ Abel summation: `∑_ρ mult(ρ)/(1+‖ρ‖²) < ∞`  (summable_mul_of_bigO_atTop)
    ⟹ band-count rate `rate k` with `∑ rate(k)/(1+k²) < ∞`
    ⟹ `hsum`  (this reduction, brick 32).

The remaining work (the engine) is to discharge the hypothesis `hrate_*` by constructing `rate`
from the Nevanlinna count. This theorem certifies that *once* such a `rate` exists, `hsum` holds. -/
theorem hsum_from_count_rate_certificate
    (M : ZeroMultiplicityData)
    (rate : ℕ → ℝ) (hrate_nonneg : ∀ k, 0 ≤ rate k)
    (hrate_count : ∀ (S : Finset {ρ : ℂ // IsNontrivialZetaZero ρ}) (k : ℕ),
      ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k), (M.mult ρ.1 : ℝ) ≤ rate k)
    (hrate_sum : Summable (fun k => rate k / (1 + (k : ℝ) ^ 2))) :
    Summable (zeroDensitySummand M) :=
  hsum_of_count_rate M rate hrate_nonneg hrate_count hrate_sum

#print axioms RHFormalization.hsum_from_count_rate_certificate

end RHFormalization
#print axioms RHFormalization.hsum_from_count_rate_certificate
