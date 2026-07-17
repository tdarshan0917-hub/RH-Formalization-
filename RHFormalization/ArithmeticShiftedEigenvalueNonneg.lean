import RHFormalization.ArithmeticShiftedPrimeDExportShiftedLaplace
import RHFormalization.PerturbedEigenvalueWeyl

/-!
# ArithmeticShiftedEigenvalueNonneg

Discharge the `hpos` hypothesis for the corrected shifted route using Weyl:

  |perturbedEigenvalue - freeEigenvalue| ≤ growthDrop V.

Important formal point:
`freeEigenvalues μ i` is Mathlib's spectral-theorem enumeration of the diagonal
operator, not definitionally `μ i`. So the clean lemma is stated using
`freeEigenvalues`.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

variable {N : ℕ}

/--
If each shifted free spectral eigenvalue dominates the perturbation norm bound,
then each shifted perturbed eigenvalue is nonnegative.
-/
theorem arithmeticShiftedPerturbedEigenvalues_nonneg_of_free_growthDrop_le
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hfree :
      ∀ i : Fin N,
        growthDrop (primePotential (primeStageWeights (N := N) n))
          ≤ freeEigenvalues (μShift μ M) i) :
    ∀ i : Fin N,
      0 ≤ perturbedEigenvalues
        (μShift μ M)
        (primePotential_isHermitian (primeStageWeights (N := N) n)) i := by
  intro i
  let V : Matrix (Fin N) (Fin N) ℂ :=
    primePotential (primeStageWeights (N := N) n)

  have hw :
      |perturbedEigenvalues
          (μShift μ M)
          (primePotential_isHermitian (primeStageWeights (N := N) n)) i
        - freeEigenvalues (μShift μ M) i|
        ≤ growthDrop V := by
    simpa [V] using
      perturbedEigenvalues_dist_le
        (μShift μ M)
        (primePotential_isHermitian (primeStageWeights (N := N) n))
        i

  -- From |a| ≤ G, get -G ≤ a.
  have hleft :
      -(growthDrop V) ≤
        perturbedEigenvalues
          (μShift μ M)
          (primePotential_isHermitian (primeStageWeights (N := N) n)) i
        - freeEigenvalues (μShift μ M) i := by
    exact (abs_le.mp hw).1

  have hlower :
      freeEigenvalues (μShift μ M) i - growthDrop V
        ≤ perturbedEigenvalues
          (μShift μ M)
          (primePotential_isHermitian (primeStageWeights (N := N) n)) i := by
    linarith

  have hnonneg :
      0 ≤ freeEigenvalues (μShift μ M) i - growthDrop V := by
    have hf := hfree i
    simpa [V] using sub_nonneg.mpr hf

  exact le_trans hnonneg hlower

#print axioms arithmeticShiftedPerturbedEigenvalues_nonneg_of_free_growthDrop_le

end

end RHFormalization
