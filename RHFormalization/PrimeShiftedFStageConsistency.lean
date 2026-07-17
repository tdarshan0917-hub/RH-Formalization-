import RHFormalization.PrimeNativeStageNonneg
import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.PrimePerturbedFStage

/-!
# PrimeShiftedFStageConsistency

Critical consistency check:

The native operator was built as

  H₀ + V_prime + M·I.

The matching F-stage should therefore be built from

  freeDiag (μ + M) + V_prime.

This file proves that matrix identity and defines the shifted F-stage.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

variable {N : ℕ}

/-- Shift the free diagonal data by the global positivity shift `M`. -/
def μShift (μ : Fin N → ℝ) (M : ℝ) : Fin N → ℝ :=
  fun i => μ i + M

/--
The shifted free-diagonal perturbed matrix is exactly the native shifted matrix.

`freeDiag(μ+M)+V_prime = freeDiag μ + V_prime + M·I`.
-/
theorem perturbedMatrix_muShift_eq_primeOpMatrix_matrix
    (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    perturbedMatrix (μShift μ M) (primePotential w)
      =
    perturbedMatrix μ (primePotential w)
      + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [primeOpMatrix_eq_diagonal μ w M]
  unfold perturbedMatrix freeDiag primePotential μShift
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.diagonal_apply, Complex.ofReal_add,
      add_assoc, add_comm, add_left_comm]
  · simp [Matrix.diagonal_apply, h]

/--
The shifted prime F-stage: the resolvent trace of the same shifted finite
operator used in `primeNativeStage`.
-/
def primeShiftedPerturbedFStage
    (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) : ℂ → ℂ :=
  primePerturbedFStage (μShift μ M) w

/-- It unfolds to the finite resolvent trace of the shifted prime spectrum. -/
theorem primeShiftedPerturbedFStage_eq
    (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) (s : ℂ) :
    primeShiftedPerturbedFStage μ w M s =
      FstageFinite
        (perturbedEigenvalues (μShift μ M) (primePotential_isHermitian w))
        s := by
  rfl

/-- Arithmetic shifted F-stage using actual prime-power stage weights. -/
def arithmeticShiftedPrimeFStage
    (n : ℕ) (μ : Fin N → ℝ) (M : ℝ) : ℂ → ℂ :=
  primeShiftedPerturbedFStage μ (primeStageWeights (N := N) n) M

#print axioms perturbedMatrix_muShift_eq_primeOpMatrix_matrix
#print axioms primeShiftedPerturbedFStage
#print axioms primeShiftedPerturbedFStage_eq
#print axioms arithmeticShiftedPrimeFStage

end

end RHFormalization
