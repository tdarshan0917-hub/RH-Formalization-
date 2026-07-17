import RHFormalization.FinitePerturbedOperator

/-!
# Gate 2: real spectrum of the finite perturbed operator

Bridges the Hermitian `perturbedMatrix` to a symmetric operator on
`EuclideanSpace ℂ (Fin N)` via `Matrix.toEuclideanLin`, using
`toEuclideanLin_conjTranspose_eq_adjoint` to get self-adjointness from
Hermitian-ness. Then its real eigenvalues come from Mathlib's finite-dim
spectral theorem (`IsSymmetric.eigenvalues`).

This is the perturbed operator with a GENUINE real spectrum — the structural
object the project was missing.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Complex

variable {N : ℕ}

/-- The perturbed operator on `EuclideanSpace ℂ (Fin N)`. -/
noncomputable def perturbedOp (μ : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanLin (perturbedMatrix μ V)

/-- The perturbed operator is symmetric (self-adjoint), from Hermitian-ness of
the matrix. -/
theorem perturbedOp_isSymmetric (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) :
    (perturbedOp μ V).IsSymmetric := by
  -- self-adjoint operator ⇒ symmetric; self-adjointness from Aᴴ = A
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  unfold perturbedOp
  rw [isSelfAdjoint_iff]
  -- adjoint (toEuclideanLin A) = toEuclideanLin Aᴴ = toEuclideanLin A
  have hconj : (perturbedMatrix μ V).conjTranspose = perturbedMatrix μ V :=
    (perturbedMatrix_isHermitian μ hV)
  have hadj := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (perturbedMatrix μ V)
  rw [hconj] at hadj
  exact hadj.symm

/-- finrank of the carrier is `N`. -/
theorem perturbedOp_finrank :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = N :=
  finrank_euclideanSpace_fin

/-- **The real eigenvalues of the finite perturbed operator** — the genuine
spectrum of `H_N = D + V`, not an assumed sequence. -/
noncomputable def perturbedEigenvalues (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) : Fin N → ℝ :=
  (perturbedOp_isSymmetric μ hV).eigenvalues perturbedOp_finrank

#print axioms perturbedOp_isSymmetric
#print axioms perturbedEigenvalues

end

end RHFormalization
