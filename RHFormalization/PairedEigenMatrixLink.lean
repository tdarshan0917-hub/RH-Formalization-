import RHFormalization.GalerkinCanonicalFSlot
import RHFormalization.PerturbedEigenvalueSum
import Mathlib

/-!
# Paired eigen ↔ matrix link — BRICK 8a-i of the canonical-F route
SENTINEL: eigen-matrix-link-v1

ROUTE CARD
1. Two lemmas translating the operator-side eigen-data of Bricks 5–7 into
   Mathlib's matrix-side spectral language, so Brick 8a-ii (the spectral-exp
   bridge) can run at matrix level via spectral_theorem + exp_units_conj:
   (i)  repo `perturbedEigenvalues` = Mathlib matrix `IsHermitian.eigenvalues`
        of `perturbedMatrix` (rfl-grade: same construction, Spectrum.lean:59);
   (ii) `pairedEigenCoeff` = star-dotProduct form `star uᵢ ⬝ᵥ (T *ᵥ uᵢ)`.
2. Pure coercion plumbing; no analysis.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

open Matrix

variable {N : ℕ}

/-- **Eigen-world link (eigenvalues)**: the repo's operator-side perturbed
eigenvalues are Mathlib's matrix-side eigenvalues of `perturbedMatrix`. -/
theorem perturbedEigenvalues_eq_matrix (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (i : Fin N) :
    perturbedEigenvalues μ hV i
      = (perturbedMatrix_isHermitian μ hV).eigenvalues i := by
  first
    | rfl
    | (unfold perturbedEigenvalues Matrix.IsHermitian.eigenvalues; rfl)
    | (unfold perturbedEigenvalues; rfl)
    | (unfold perturbedEigenvalues Matrix.IsHermitian.eigenvalues
       congr 1)

/-- **Eigen-world link (basis)**: the repo's operator-side eigenvector basis
is Mathlib's matrix-side one. -/
theorem perturbedEigenvectorBasis_eq_matrix (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) :
    ((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank)
      = (perturbedMatrix_isHermitian μ hV).eigenvectorBasis := by
  first
    | rfl
    | (unfold Matrix.IsHermitian.eigenvectorBasis; rfl)
    | (unfold Matrix.IsHermitian.eigenvectorBasis
       congr 1)

/-- **Paired coefficient in matrix dotProduct form**:
`pairedEigenCoeff = star uᵢ ⬝ᵥ (T *ᵥ uᵢ)` with `uᵢ` the i-th matrix
eigenvector. -/
theorem pairedEigenCoeff_eq_dotProduct (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    pairedEigenCoeff (N := N) μ hV T i
      = dotProduct
          (star ⇑((perturbedMatrix_isHermitian μ hV).eigenvectorBasis i))
          (T *ᵥ ⇑((perturbedMatrix_isHermitian μ hV).eigenvectorBasis i)) := by
  unfold pairedEigenCoeff
  rw [perturbedEigenvectorBasis_eq_matrix μ hV]
  set u := (perturbedMatrix_isHermitian μ hV).eigenvectorBasis i with hu
  first
    | (rw [EuclideanSpace.inner_eq_star_dotProduct]
       congr 1
       first
         | (rw [Matrix.toEuclideanLin_eq_toLin]
            rfl)
         | rfl
         | simp [Matrix.toEuclideanLin_eq_toLin, Matrix.toLin_apply,
             Matrix.mulVec, dotProduct])
    | (simp [EuclideanSpace.inner_eq_star_dotProduct,
        Matrix.toEuclideanLin_eq_toLin, Matrix.toLin_apply])
    | (rw [show inner ℂ u ((Matrix.toEuclideanLin T) u)
          = dotProduct (star ⇑u) ((Matrix.toEuclideanLin T) u : _) from
            EuclideanSpace.inner_eq_star_dotProduct _ _]
       congr 1
       rfl)

#print axioms perturbedEigenvalues_eq_matrix
#print axioms perturbedEigenvectorBasis_eq_matrix
#print axioms pairedEigenCoeff_eq_dotProduct

end

end RHFormalization
