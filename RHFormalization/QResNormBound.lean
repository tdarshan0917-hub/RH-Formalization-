import RHFormalization.ResidualLaplaceRep
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import Mathlib

/-!
# Pointwise norm bound on qResIntegrand (Leaf 2, rung 1).

‖Q_res(t)‖ ≤ ‖F-part‖ + ‖spike-part‖, via triangle inequality.
Foundation for the cutoff-independent ∫‖Q_res‖ ≤ C bound (hQint).
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- **Pointwise F-part norm bound.** ‖∑ᵢ e^{-(s+λᵢ)t}‖ ≤ ∑ᵢ e^{-(Re s + λᵢ)t}. -/
theorem norm_fPart_le
    (n : ℕ) (μ : Fin N → ℝ) (s : ℂ) (t : ℝ) :
    ‖∑ i, Complex.exp (-(s +
        ((perturbedEigenvalues μ (primePotential_isHermitian
          (primeStageWeights (N := N) n)) i : ℝ) : ℂ)) * (t:ℂ))‖
      ≤ ∑ i, Real.exp (-(s.re +
          (perturbedEigenvalues μ (primePotential_isHermitian
            (primeStageWeights (N := N) n)) i)) * t) := by
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro i _
  rw [Complex.norm_exp]
  apply le_of_eq
  congr 1
  simp [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
        Complex.neg_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im]

#print axioms norm_fPart_le

end RHFormalization
