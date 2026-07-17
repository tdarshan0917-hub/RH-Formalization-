import RHFormalization.ArithmeticPrimeActiveCenterNonneg
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# ArithmeticShiftedEigenvalueNonnegFromPositive

Fixed target:

Prove the final local positivity bridge

  hnn ⇒ shifted perturbed eigenvalues are nonnegative.

This removes the last local finite-stage hypothesis `hfree` once wired into
the corrected shifted-Laplace DExport theorem.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

variable {N : ℕ}

/--
The shifted perturbed operator is positive if the shifted native quadratic form
is nonnegative.
-/
theorem shiftedPerturbedOp_isPositive_of_hnn
    (μ : Fin N → ℝ)
    (w : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ w M y))) :
    (perturbedOp (μShift μ M) (primePotential w)).IsPositive := by
  rw [LinearMap.isPositive_iff_complex]
  intro y
  constructor
  ·
    have hsym :
        (perturbedOp (μShift μ M) (primePotential w)).IsSymmetric :=
      perturbedOp_isSymmetric (μShift μ M) (primePotential_isHermitian w)
    exact hsym.coe_re_inner_apply_self y
  ·
    have hop :
        perturbedOp (μShift μ M) (primePotential w)
          =
        (primeOpCLM μ w M :
          EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) := by
      unfold perturbedOp primeOpCLM
      rw [perturbedMatrix_muShift_eq_primeOpMatrix_matrix]
      exact
        (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin
          (n := Fin N)
          (𝕜 := ℂ)
          (perturbedMatrix μ (primePotential w)
            + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).symm

    have hnn' : 0 ≤ (inner ℂ y ((primeOpCLM μ w M) y)).re := by
      simpa using hnn y

    have hswap :
        (inner ℂ y ((primeOpCLM μ w M) y)).re
          =
        (inner ℂ ((primeOpCLM μ w M) y) y).re := by
      simpa using
        inner_re_symm (𝕜 := ℂ) y ((primeOpCLM μ w M) y)

    have hgoal :
        0 ≤ (inner ℂ ((primeOpCLM μ w M) y) y).re := by
      simpa [hswap] using hnn'

    rw [hop]
    simpa using hgoal

/--
Direct nonnegativity of the shifted arithmetic perturbed eigenvalues from the
native nonnegative quadratic form.
-/
theorem arithmeticShiftedPerturbedEigenvalues_nonneg_of_hnn
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights (N := N) n) M y))) :
    ∀ i : Fin N,
      0 ≤ perturbedEigenvalues
        (μShift μ M)
        (primePotential_isHermitian (primeStageWeights (N := N) n)) i := by
  intro i
  let T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    perturbedOp (μShift μ M) (primePotential (primeStageWeights (N := N) n))

  have hTpos : T.IsPositive := by
    simpa [T] using
      shiftedPerturbedOp_isPositive_of_hnn
        μ
        (primeStageWeights (N := N) n)
        M
        hnn

  have hnon :=
    LinearMap.IsPositive.nonneg_eigenvalues
      (T := T)
      (n := N)
      hTpos
      perturbedOp_finrank
      i

  simpa [T, perturbedEigenvalues] using hnon

#print axioms shiftedPerturbedOp_isPositive_of_hnn
#print axioms arithmeticShiftedPerturbedEigenvalues_nonneg_of_hnn

end

end RHFormalization
