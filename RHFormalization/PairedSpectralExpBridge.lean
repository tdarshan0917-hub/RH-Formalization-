import RHFormalization.MatrixExpEigenvector
import RHFormalization.GalerkinCanonicalFHolo
import RHFormalization.GalerkinPairedPerturbedLaplace
import Mathlib

/-!
# Paired spectral-exp bridge — BRICK 8a-iii of the canonical-F route
SENTINEL: paired-spectral-exp-v1

ROUTE CARD
1. `perturbedMatrix_mulVec_eigenbasis`: the repo eigenbasis satisfies the
   MATRIX eigen-relation (transport of `apply_eigenvectorBasis` through
   `ofLp_toEuclideanLin_apply`).
2. `exp_perturbedMatrix_mulVec_eigenbasis`: 8a-ii applied — the matrix exp
   of `(−t:ℂ) • perturbedMatrix` acts by `e^{−tλᵢ}` on the eigenbasis.
3. Everything at the repo's own eigen-data — Mathlib's matrix eigen-layer
   (equivOfCardEq reindex) deliberately never enters.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Shorthand: the repo's perturbed eigenbasis vector as a plain function. -/
def perturbedEigvec (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (i : Fin N) :
    Fin N → ℂ :=
  WithLp.ofLp
    (((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) i)

/-- **The matrix eigen-relation for the repo eigenbasis**: transporting the
operator relation `perturbedOp bᵢ = λᵢ • bᵢ` through `ofLp`. -/
theorem perturbedMatrix_mulVec_eigenbasis (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (i : Fin N) :
    Matrix.mulVec (perturbedMatrix μ V) (perturbedEigvec μ hV i)
      = ((perturbedEigenvalues μ hV i : ℝ) : ℂ) • perturbedEigvec μ hV i := by
  have hop := (perturbedOp_isSymmetric μ hV).apply_eigenvectorBasis
    perturbedOp_finrank i
  -- perturbedOp = toEuclideanLin (perturbedMatrix); unfold and push ofLp
  have hop' : (Matrix.toEuclideanLin (perturbedMatrix μ V))
      (((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) i)
      = ((perturbedEigenvalues μ hV i : ℝ) : ℂ) •
          (((perturbedOp_isSymmetric μ hV).eigenvectorBasis
            perturbedOp_finrank) i) := by
    first
      | exact hop
      | (unfold perturbedEigenvalues
         exact hop)
      | (have := hop
         unfold perturbedOp at this
         exact this)
  have hofLp := congrArg WithLp.ofLp hop'
  first
    | (rw [Matrix.ofLp_toEuclideanLin_apply] at hofLp
       unfold perturbedEigvec
       first
         | exact hofLp
         | simpa using hofLp)
    | (unfold perturbedEigvec
       first
         | (rw [← Matrix.ofLp_toEuclideanLin_apply]
            exact hofLp)
         | simpa [Matrix.ofLp_toEuclideanLin_apply] using hofLp)

/-- **The exp eigen-relation**: `exp((−t:ℂ) • perturbedMatrix)` acts by
`exp(−t·λᵢ)` on the repo eigenbasis. 8a-ii fired at the scaled matrix. -/
theorem exp_perturbedMatrix_mulVec_eigenbasis (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (t : ℝ) (i : Fin N) :
    Matrix.mulVec
        (NormedSpace.exp ((-(t : ℂ)) • perturbedMatrix μ V))
        (perturbedEigvec μ hV i)
      = Complex.exp (-(t : ℂ) *
          ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) • perturbedEigvec μ hV i := by
  have hscaled : Matrix.mulVec ((-(t : ℂ)) • perturbedMatrix μ V)
      (perturbedEigvec μ hV i)
      = ((-(t : ℂ)) * ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) •
          perturbedEigvec μ hV i := by
    rw [Matrix.smul_mulVec, perturbedMatrix_mulVec_eigenbasis μ hV i,
      smul_smul]
  have h := matrix_exp_mulVec_eigenvector
    ((-(t : ℂ)) • perturbedMatrix μ V)
    (perturbedEigvec μ hV i)
    ((-(t : ℂ)) * ((perturbedEigenvalues μ hV i : ℝ) : ℂ))
    hscaled
  rw [h]
  congr 1
  first
    | exact (Complex.exp_eq_exp_ℂ ▸ rfl)
    | rfl
    | simp [NormedSpace.exp_eq_exp_ℂ]
    | rw [Complex.exp_eq_exp_ℂ]

#print axioms perturbedEigvec
#print axioms perturbedMatrix_mulVec_eigenbasis
#print axioms exp_perturbedMatrix_mulVec_eigenbasis

end

end RHFormalization
