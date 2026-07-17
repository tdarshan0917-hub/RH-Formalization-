import RHFormalization.PrimeHeatTrace
import RHFormalization.FiniteHeatTraceDiagonal
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Diagonal heat-weight matrix `e^{-t μ}` for the prime operator's diagonal `μ`. -/
noncomputable def primeHeatWeightMatrix (μ : Fin N → ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => Complex.exp (-(t : ℂ) * (μ i : ℂ)))

/-- Order-2 Duhamel integrand for the prime operator. -/
noncomputable def primeDuhamel2Integrand
    (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) (t u : ℝ) : ℂ :=
  (V * primeHeatWeightMatrix μ (t - u) * V * primeHeatWeightMatrix μ u).trace

/-- General complex trace identity (port of Galerkin `trace_V_diag_V_diag`). -/
theorem trace_V_diagC_V_diagC
    (V : Matrix (Fin N) (Fin N) ℂ) (d₁ d₂ : Fin N → ℂ) :
    (V * Matrix.diagonal d₁ * V * Matrix.diagonal d₂).trace
      = ∑ m, ∑ n, V m n * d₁ n * V n m * d₂ m := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro m _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  have hdiag : ∀ k, (V * Matrix.diagonal d₁ * V) m k * Matrix.diagonal d₂ k m
      = if k = m then (V * Matrix.diagonal d₁ * V) m m * d₂ m else 0 := by
    intro k
    rw [Matrix.diagonal_apply]
    split
    · next h => subst h; ring
    · ring
  simp only [hdiag]
  rw [Finset.sum_ite_eq' Finset.univ m]
  simp only [Finset.mem_univ, if_true]
  rw [Matrix.mul_apply]
  have hinner : ∀ n, (V * Matrix.diagonal d₁) m n * V n m
      = V m n * d₁ n * V n m := by
    intro n
    rw [Matrix.mul_apply]
    have hk : ∀ k, V m k * Matrix.diagonal d₁ k n = if k = n then V m n * d₁ n else 0 := by
      intro k; rw [Matrix.diagonal_apply]; split
      · next h => subst h; ring
      · ring
    simp only [hk]
    rw [Finset.sum_ite_eq' Finset.univ n]
    simp only [Finset.mem_univ, if_true]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [hinner]

theorem primeDuhamel2Integrand_eq_sum
    (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) (t u : ℝ) :
    primeDuhamel2Integrand μ V t u
      = ∑ m : Fin N, ∑ n : Fin N,
          V m n
          * Complex.exp (-((t - u : ℝ) : ℂ) * (μ n : ℂ))
          * V n m
          * Complex.exp (-((u : ℝ) : ℂ) * (μ m : ℂ)) := by
  unfold primeDuhamel2Integrand primeHeatWeightMatrix
  rw [trace_V_diagC_V_diagC]

#print axioms primeDuhamel2Integrand_eq_sum

end
end RHFormalization
