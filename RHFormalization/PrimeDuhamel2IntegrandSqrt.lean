import RHFormalization.PrimeDuhamel2IntegrandBound
import RHFormalization.PrimeHeatSumBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- **Brick 3b (integrand sqrt bound).** With a uniform entry bound `‖V_{ij}‖ ≤ B` and
eigenvalue growth, the prime order-2 Duhamel integrand satisfies the integrable
sqrt-product bound `‖·‖ ≤ B²·N·(√(π/((t-u)c))/2)·(√(π/(uc))/2)·e^{2tM}`. -/
theorem norm_primeDuhamel2Integrand_le_sqrt
    (L : ℝ) (hL : 0 < L) (M : ℝ) (B : ℝ) (hB : 0 ≤ B)
    (t u : ℝ) (hu : 0 < u) (htu : 0 < t - u)
    (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ)
    (hVB : ∀ i j, ‖V i j‖ ≤ B)
    (hμ : ∀ n : Fin N, ((((n : ℝ) + 1) * Real.pi / L) ^ 2) - M ≤ μ n) :
    ‖primeDuhamel2Integrand μ V t u‖
      ≤ B ^ 2
          * (Real.exp ((t - u) * M) * (Real.sqrt (Real.pi / ((t - u) * (Real.pi / L) ^ 2)) / 2))
          * (Real.exp (u * M) * (Real.sqrt (Real.pi / (u * (Real.pi / L) ^ 2)) / 2)) := by
  refine le_trans (norm_primeDuhamel2Integrand_le μ V t u) ?_
  -- bound the double sum by B²·(∑_n e^{-(t-u)μ_n})·(∑_m e^{-uμ_m})
  have hfactor : ∑ m : Fin N, ∑ n : Fin N,
        ‖V m n‖ * ‖V n m‖ * Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m)
      ≤ ∑ m : Fin N, ∑ n : Fin N,
        B ^ 2 * Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m) := by
    apply Finset.sum_le_sum; intro m _
    apply Finset.sum_le_sum; intro n _
    have hVmn := hVB m n
    have hVnm := hVB n m
    have hee : 0 ≤ Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m) :=
      mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    have hVV : ‖V m n‖ * ‖V n m‖ ≤ B ^ 2 := by
      calc ‖V m n‖ * ‖V n m‖ ≤ B * B :=
            mul_le_mul hVmn hVnm (norm_nonneg _) hB
        _ = B ^ 2 := by ring
    calc ‖V m n‖ * ‖V n m‖ * Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m)
        = (‖V m n‖ * ‖V n m‖) * (Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m)) := by ring
      _ ≤ B ^ 2 * (Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m)) :=
          mul_le_mul_of_nonneg_right hVV hee
      _ = B ^ 2 * Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m) := by ring
  refine le_trans hfactor ?_
  -- factor: ∑_m ∑_n B² e_n e_m = B²·(∑_n e_n)·(∑_m e_m)
  have hsplit : ∑ m : Fin N, ∑ n : Fin N,
        B ^ 2 * Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m)
      = B ^ 2 * ((∑ n : Fin N, Real.exp (-(t - u) * μ n))
                  * (∑ m : Fin N, Real.exp (-u * μ m))) := by
    have key : (∑ n : Fin N, Real.exp (-(t - u) * μ n))
                * (∑ m : Fin N, Real.exp (-u * μ m))
        = ∑ m : Fin N, ∑ n : Fin N,
            Real.exp (-(t - u) * μ n) * Real.exp (-u * μ m) := by
      rw [Finset.sum_comm]
      rw [← Finset.sum_mul_sum]
    rw [key, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [hsplit]
  -- apply brick 3a to each heat sum
  have hn := prime_heat_sum_sqrt_bound L hL M (t - u) htu μ hμ
  have hm := prime_heat_sum_sqrt_bound L hL M u hu μ hμ
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
  have hsm_nonneg : 0 ≤ ∑ m : Fin N, Real.exp (-u * μ m) :=
    Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)
  have hbound_n_nonneg : 0 ≤ Real.exp ((t - u) * M) * (Real.sqrt (Real.pi / ((t - u) * (Real.pi / L) ^ 2)) / 2) := by
    apply mul_nonneg (Real.exp_nonneg _); positivity
  calc B ^ 2 * ((∑ n : Fin N, Real.exp (-(t - u) * μ n))
                * (∑ m : Fin N, Real.exp (-u * μ m)))
      ≤ B ^ 2 * ((Real.exp ((t - u) * M) * (Real.sqrt (Real.pi / ((t - u) * (Real.pi / L) ^ 2)) / 2))
                * (Real.exp (u * M) * (Real.sqrt (Real.pi / (u * (Real.pi / L) ^ 2)) / 2))) := by
        apply mul_le_mul_of_nonneg_left _ hB2
        exact mul_le_mul hn hm hsm_nonneg hbound_n_nonneg
    _ = B ^ 2
          * (Real.exp ((t - u) * M) * (Real.sqrt (Real.pi / ((t - u) * (Real.pi / L) ^ 2)) / 2))
          * (Real.exp (u * M) * (Real.sqrt (Real.pi / (u * (Real.pi / L) ^ 2)) / 2)) := by ring

#print axioms norm_primeDuhamel2Integrand_le_sqrt

end
end RHFormalization
