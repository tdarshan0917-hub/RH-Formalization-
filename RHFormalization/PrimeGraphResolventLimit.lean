import RHFormalization.PrimeGraphResolvent
import Mathlib

/-!
# PrimeGraphResolventLimit — PG-3: the full orbit sum converges to the resolvent trace

If `1 - U` is invertible and `U^M → 0`, then
`Tr(Λ Σ_{m<M} U^m) → Tr(Λ (1 - U)⁻¹)`.
This is the prime-graph trace formula's orbit expansion, summed exactly.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix Filter Topology
open scoped BigOperators

/-- **PG-3**: the weighted orbit sums converge to the resolvent trace. -/
theorem trace_orbit_sum_tendsto_resolvent {n : Type*} [Fintype n] [DecidableEq n]
    (Λ U : Matrix n n ℂ) (h : IsUnit (1 - U).det)
    (hU : Tendsto (fun M : ℕ => U ^ M) atTop (𝓝 0)) :
    Tendsto (fun M : ℕ => Matrix.trace (Λ * ∑ m ∈ Finset.range M, U ^ m)) atTop
      (𝓝 (Matrix.trace (Λ * (1 - U)⁻¹))) := by
  have hc : Continuous (fun A : Matrix n n ℂ => Matrix.trace (Λ * ((1 - A) * (1 - U)⁻¹))) := by
    first
      | fun_prop
      | exact (continuous_const.matrix_mul
          ((continuous_const.sub continuous_id).matrix_mul continuous_const)).matrix_trace
  have hlim := (hc.tendsto 0).comp hU
  simp only [sub_zero, one_mul] at hlim
  refine hlim.congr (fun M => ?_)
  exact (trace_orbit_sum_resolvent Λ U h M).symm

#print axioms trace_orbit_sum_tendsto_resolvent

end RHFormalization
