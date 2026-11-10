import RHFormalization.PrimeGraphJacobi
import Mathlib

/-!
# PrimeGraphTraceFormula — PG-7: log-derivative of the secular determinant = orbit sum

For `U = U(x) = diag(p^{ix})·σ`, `σ` unitary, `Im x > 0`:
`Σ_{m=1}^{M} Tr(Λ U^m) → i · (det(1-U))'(x) / det(1-U(x))`, with `Λ = diag(log p)`.
Left: periodic-orbit sum. Right: log-derivative of the secular determinant, whose zeros are the
graph's levels (all real, PG-5). This is the graph's explicit formula as one theorem.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix Filter Topology
open scoped BigOperators

/-- **PG-7 — the prime-graph trace formula.** -/
theorem primeGraph_logDeriv_eq_orbit_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ)
    (hσ : σ ∈ unitary (Matrix ι ι ℂ)) (x : ℂ) (hx : 0 < x.im) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M,
        (Matrix.diagonal (fun b => Complex.log ((pr b : ℕ) : ℂ)) * graphU pr σ x ^ (m + 1)).trace)
      atTop
      (𝓝 (Complex.I * (deriv (fun k => (1 - graphU pr σ k).det) x
        / (1 - graphU pr σ x).det))) := by
  have hz : ∀ b, ‖((pr b : ℕ) : ℂ) ^ (Complex.I * x)‖ < 1 :=
    fun b => primePhase_norm_lt_one (hpr b) hx
  have hunit : IsUnit (1 - graphU pr σ x).det := graphMap_one_sub_isUnit_det _ σ hσ hz
  have hpow : Tendsto (fun M : ℕ => graphU pr σ x ^ M) atTop (𝓝 0) :=
    graphMap_pow_tendsto_zero _ σ hσ hz
  have hlim := trace_orbit_sum_tendsto_resolvent
    (Matrix.diagonal (fun b => Complex.log ((pr b : ℕ) : ℂ)) * graphU pr σ x)
    (graphU pr σ x) hunit hpow
  have hd := secularDet_hasDerivAt_upper pr hpr σ hσ x hx
  have hdet0 : (1 - graphU pr σ x).det ≠ 0 := hunit.ne_zero
  have hT : ((1 - graphU pr σ x)⁻¹ * -(Complex.I • (Matrix.diagonal
        (fun b => Complex.log ((pr b : ℕ) : ℂ)) * graphU pr σ x))).trace
      = -(Complex.I * (Matrix.diagonal (fun b => Complex.log ((pr b : ℕ) : ℂ))
          * graphU pr σ x * (1 - graphU pr σ x)⁻¹).trace) := by
    rw [Matrix.mul_neg, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm]
  have hval : Complex.I * ((1 - graphU pr σ x).det *
        ((1 - graphU pr σ x)⁻¹ * -(Complex.I • (Matrix.diagonal
          (fun b => Complex.log ((pr b : ℕ) : ℂ)) * graphU pr σ x))).trace
        / (1 - graphU pr σ x).det)
      = (Matrix.diagonal (fun b => Complex.log ((pr b : ℕ) : ℂ))
          * graphU pr σ x * (1 - graphU pr σ x)⁻¹).trace := by
    rw [mul_comm ((1 - graphU pr σ x).det), mul_div_assoc, div_self hdet0, mul_one, hT]
    linear_combination (-(Matrix.diagonal (fun b => Complex.log ((pr b : ℕ) : ℂ))
      * graphU pr σ x * (1 - graphU pr σ x)⁻¹).trace) * Complex.I_mul_I
  rw [hd.deriv, hval]
  refine hlim.congr (fun M => ?_)
  rw [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [pow_succ', mul_assoc]

#print axioms primeGraph_logDeriv_eq_orbit_sum

end RHFormalization
