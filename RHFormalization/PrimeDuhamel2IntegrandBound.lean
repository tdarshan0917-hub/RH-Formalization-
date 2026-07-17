import RHFormalization.PrimeDuhamel2Integrand
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Complex
open scoped BigOperators

variable {N : ℕ}

/-- Norm of a real-scalar-times-complex exp: `‖exp(-(x:ℝ)·(μ:ℝ))‖ = exp(-x·μ)`. -/
theorem norm_exp_neg_real (x y : ℝ) :
    ‖Complex.exp (-((x : ℝ) : ℂ) * (y : ℂ))‖ = Real.exp (-x * y) := by
  rw [Complex.norm_exp]
  congr 1
  have : (-((x : ℝ) : ℂ) * (y : ℂ)) = ((-x * y : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- **Brick 2**: pointwise norm bound on the prime order-2 Duhamel integrand. -/
theorem norm_primeDuhamel2Integrand_le
    (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) (t u : ℝ) :
    ‖primeDuhamel2Integrand μ V t u‖
      ≤ ∑ m : Fin N, ∑ n : Fin N,
          ‖V m n‖ * ‖V n m‖
          * Real.exp (-(t - u) * μ n)
          * Real.exp (-u * μ m) := by
  rw [primeDuhamel2Integrand_eq_sum]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro m _
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul, norm_mul, norm_mul, norm_exp_neg_real, norm_exp_neg_real]
  apply le_of_eq
  ring

#print axioms norm_primeDuhamel2Integrand_le

end
end RHFormalization
