import RHFormalization.PrimeNativeStageAssembly
import Mathlib

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike Complex

variable {N : ℕ}

/-- The prime operator matrix is the single diagonal `diagonal(μ_k + w_k + M)`. -/
theorem primeOpMatrix_eq_diagonal (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    perturbedMatrix μ (primePotential w) + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.diagonal (fun k => ((μ k + w k + M : ℝ) : ℂ)) := by
  unfold perturbedMatrix freeDiag primePotential
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : i = j
  · subst h; simp [Complex.ofReal_add]
  · simp [h]

/-- The quadratic form of the prime operator: `re⟨y, H y⟩ = Σ (μ_k+w_k+M)|y_k|²`. -/
theorem primeOpCLM_form_eq_sum (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ)
    (y : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ y (primeOpCLM μ w M y))
      = ∑ k, (μ k + w k + M) * ‖y k‖ ^ 2 := by
  unfold primeOpCLM
  rw [primeOpMatrix_eq_diagonal, PiLp.inner_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  -- the k-th coordinate of toEuclideanCLM(diagonal d) y is d_k * y_k (via ofLp = rfl, mulVec_diagonal)
  have happ : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)
      (Matrix.diagonal (fun j => ((μ j + w j + M : ℝ) : ℂ))) y) k
      = ((μ k + w k + M : ℝ) : ℂ) * y k := by
    show ((Matrix.diagonal (fun j => ((μ j + w j + M : ℝ) : ℂ))) *ᵥ (y : Fin N → ℂ)) k
        = ((μ k + w k + M : ℝ) : ℂ) * y k
    rw [Matrix.mulVec_diagonal]
  rw [RCLike.inner_apply, happ]
  have hconj : y k * (starRingEnd ℂ) (y k) = ((‖y k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hfactor : ((μ k + w k + M : ℝ) : ℂ) * y k * (starRingEnd ℂ) (y k)
      = ((μ k + w k + M : ℝ) : ℂ) * ((‖y k‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, hconj]
  rw [hfactor, ← Complex.ofReal_mul]
  norm_cast

#print axioms primeOpMatrix_eq_diagonal
#print axioms primeOpCLM_form_eq_sum
end
end RHFormalization
