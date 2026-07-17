import RHFormalization.PerturbedGroundStateFormBound
import RHFormalization.MinMaxBrick10

namespace RHFormalization
noncomputable section
open Matrix Complex RCLike

variable {N : ℕ}

/-- The free diagonal operator is symmetric (real diagonal matrix is Hermitian). -/
theorem freeDiagOp_isSymmetric (μ : Fin N → ℝ) : (freeDiagOp μ).IsSymmetric := by
  rw [freeDiagOp, Matrix.isSymmetric_toEuclideanLin_iff]
  exact freeDiag_isHermitian μ

/-- The free eigenvalues — the spectrum of the unperturbed diagonal operator `D`. -/
noncomputable def freeEigenvalues (μ : Fin N → ℝ) : Fin N → ℝ :=
  (freeDiagOp_isSymmetric μ).eigenvalues perturbedOp_finrank

/-- **Form upper bound.** `re⟨H_N x, x⟩ ≤ re⟨D x, x⟩ + ‖V_op‖·‖x‖²`. -/
theorem perturbedOp_formUpperBound (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ (perturbedOp μ V x) x)
      ≤ RCLike.re (inner ℂ (freeDiagOp μ x) x) + growthDrop V * ‖x‖ ^ 2 := by
  have hsplit : perturbedOp μ V x = freeDiagOp μ x + pertOp V x := by
    rw [perturbedOp_eq_add]; rfl
  have hre : RCLike.re (inner ℂ (perturbedOp μ V x) x)
      = RCLike.re (inner ℂ (freeDiagOp μ x) x) + RCLike.re (inner ℂ (pertOp V x) x) := by
    rw [hsplit, inner_add_left, map_add]
  have hVx : ‖(pertOp V) x‖ ≤ growthDrop V * ‖x‖ := by
    unfold growthDrop
    exact (LinearMap.toContinuousLinearMap (pertOp V)).le_opNorm x
  have hup : RCLike.re (inner ℂ ((pertOp V) x) x) ≤ ‖(pertOp V) x‖ * ‖x‖ :=
    re_inner_le_norm (𝕜 := ℂ) _ _
  have hstep : ‖(pertOp V) x‖ * ‖x‖ ≤ growthDrop V * ‖x‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right hVx (norm_nonneg _)
  have hsq : growthDrop V * ‖x‖ * ‖x‖ = growthDrop V * ‖x‖ ^ 2 := by ring
  rw [hre]; linarith [hup, hstep, hsq.le, hsq.ge]

/-- Argument-order interchange for the real part of an inner product. -/
theorem re_inner_comm (op : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (x : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ (op x) x) = RCLike.re (inner ℂ x (op x)) := by
  rw [← inner_conj_symm (op x) x, RCLike.conj_re]

/-- **Two-sided form distance.** `|re⟨x, H_N x⟩ − re⟨x, D x⟩| ≤ ‖V_op‖·‖x‖²`. -/
theorem perturbedOp_formDist (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    |RCLike.re (inner ℂ x (perturbedOp μ V x)) - RCLike.re (inner ℂ x (freeDiagOp μ x))|
      ≤ growthDrop V * ‖x‖ ^ 2 := by
  rw [← re_inner_comm, ← re_inner_comm, abs_le]
  refine ⟨?_, ?_⟩
  · linarith [perturbedOp_formLowerBound μ V x]
  · linarith [perturbedOp_formUpperBound μ V x]

/-- **Per-eigenvalue perturbation control for `H_N = D + V`.**
`|λ_k(D + V) − λ_k(D)| ≤ ‖V_op‖` for every index `k`. This is Weyl's inequality applied to
the prime-weighted operator: the perturbed spectrum cannot drift more than `‖V‖` from the
free spectrum, eigenvalue by eigenvalue — the operator-side per-eigenvalue control. -/
theorem perturbedEigenvalues_dist_le (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (k : Fin N) :
    |perturbedEigenvalues μ hV k - freeEigenvalues μ k| ≤ growthDrop V :=
  eigenvalues_dist_le (perturbedOp_isSymmetric μ hV) (freeDiagOp_isSymmetric μ)
    perturbedOp_finrank (growthDrop V) (perturbedOp_formDist μ V) k

#print axioms perturbedEigenvalues_dist_le
end
end RHFormalization
