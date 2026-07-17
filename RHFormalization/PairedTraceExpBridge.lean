import RHFormalization.PairedSpectralExpBridge
import RHFormalization.AdmissibleFirstOrderDiagonal
import Mathlib

/-!
# Paired trace-exp bridge — BRICK 8a-iv of the canonical-F route
SENTINEL: paired-trace-exp-v2

ROUTE CARD
1. THE ASSEMBLY: `Tr(exp((−t:ℂ)•perturbedMatrix)·T) = pairedPerturbedHeatTrace`
   — the matrix-exp world (Duhamel tower side) meets the eigen-sum world
   (Bricks 5–7 transform side) in one identity.
2. Route: trace cyclicity → banked trace_toEuclideanLin →
   LinearMap.trace_eq_sum_inner on the repo eigenbasis →
   banked toEuclideanLin_mul_eq → 8a-iii diagonal action → inner_smul_right.
3. v2: removed the stray misnamed `have` that poisoned v1's first-chain.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- 8a-iii lifted back to EuclideanSpace level: `toEuclideanLin (exp)` acts
diagonally on the repo eigenbasis. -/
theorem toEuclideanLin_exp_eigenbasis (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (t : ℝ) (i : Fin N) :
    (Matrix.toEuclideanLin
        (NormedSpace.exp ((-(t : ℂ)) • perturbedMatrix μ V)))
      (((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) i)
      = Complex.exp (-(t : ℂ) * ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) •
          (((perturbedOp_isSymmetric μ hV).eigenvectorBasis
            perturbedOp_finrank) i) := by
  have h := exp_perturbedMatrix_mulVec_eigenbasis μ hV t i
  first
    | (apply (WithLp.ofLp_injective 2)
       first
         | (rw [Matrix.ofLp_toEuclideanLin_apply]
            simpa [perturbedEigvec] using h)
         | simpa [Matrix.ofLp_toEuclideanLin_apply, perturbedEigvec] using h)
    | (have hlift := congrArg (WithLp.toLp 2) h
       first
         | simpa [perturbedEigvec, Matrix.toEuclideanLin_apply] using hlift
         | (unfold perturbedEigvec at hlift
            simpa [Matrix.toEuclideanLin_apply] using hlift))
    | (ext j
       have hj := congrFun h j
       simpa [perturbedEigvec, Matrix.ofLp_toEuclideanLin_apply] using hj)

/-- **BRICK 8a-iv — THE PAIRED TRACE-EXP BRIDGE.** -/
theorem trace_exp_mul_eq_pairedHeatTrace (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    ((NormedSpace.exp ((-(t : ℂ)) • perturbedMatrix μ V)) * T).trace
      = pairedPerturbedHeatTrace (N := N) μ hV T t := by
  rw [Matrix.trace_mul_comm]
  rw [← trace_toEuclideanLin]
  rw [LinearMap.trace_eq_sum_inner _
    (((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank))]
  unfold pairedPerturbedHeatTrace
  refine Finset.sum_congr rfl fun i _ => ?_
  have hact : (Matrix.toEuclideanLin
      (T * NormedSpace.exp ((-(t : ℂ)) • perturbedMatrix μ V)))
      (((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) i)
      = Complex.exp (-(t : ℂ) * ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) •
          ((Matrix.toEuclideanLin T)
            (((perturbedOp_isSymmetric μ hV).eigenvectorBasis
              perturbedOp_finrank) i)) := by
    rw [toEuclideanLin_mul_eq]
    first
      | (rw [LinearMap.mul_apply, toEuclideanLin_exp_eigenbasis μ hV t i,
           map_smul])
      | (simp only [LinearMap.mul_apply]
         rw [toEuclideanLin_exp_eigenbasis μ hV t i, map_smul])
      | (show (Matrix.toEuclideanLin T) ((Matrix.toEuclideanLin
           (NormedSpace.exp ((-(t : ℂ)) • perturbedMatrix μ V)))
           (((perturbedOp_isSymmetric μ hV).eigenvectorBasis
             perturbedOp_finrank) i)) = _
         rw [toEuclideanLin_exp_eigenbasis μ hV t i, map_smul])
  rw [hact]
  first
    | (rw [inner_smul_right]
       unfold pairedEigenCoeff
       ring)
    | (rw [inner_smul_right_eq_smul]
       unfold pairedEigenCoeff
       first
         | (rw [smul_eq_mul]; ring)
         | ring)
    | (unfold pairedEigenCoeff
       simp [inner_smul_right, mul_comm])

#print axioms toEuclideanLin_exp_eigenbasis
#print axioms trace_exp_mul_eq_pairedHeatTrace

end

end RHFormalization
