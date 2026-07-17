import RHFormalization.QResNormBound
import RHFormalization.QResSpikeNormBound
import Mathlib

/-!
# Combined pointwise bound on ‖qResIntegrand‖ (Leaf 2, rung 3).

‖Q_res(t)‖ = ‖F-part − spike-part‖ ≤ ‖F-part‖ + ‖spike-part‖
           ≤ (∑ᵢ e^{-(Re s+λᵢ)t}) + (∑_q |contribution|·e^{-Re(s)t}·e^{-t/4}·heatKernelRealScalar).
Combines norm_fPart_le + norm_spikePart_le via the subtraction triangle.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- **Combined pointwise norm bound on Q_res.** -/
theorem norm_qResIntegrand_le
    (n : ℕ) (μ : Fin N → ℝ) (α : DFiniteStage) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖qResIntegrand n μ α s t‖
      ≤ (∑ i, Real.exp (-(s.re +
            (perturbedEigenvalues μ (primePotential_isHermitian
              (primeStageWeights (N := N) n)) i)) * t))
        + (∑ q ∈ α.diagonalSpikeActiveIndices,
            ‖α.diagonalSpikeContribution q‖ *
              (Real.exp (-s.re * t) * Real.exp (-t/4) *
                heatKernelRealScalar t (PrimePowerPair.center (α.diagonalSpikeToPP q)))) := by
  unfold qResIntegrand
  refine le_trans (norm_sub_le _ _) ?_
  exact add_le_add (norm_fPart_le n μ s t) (norm_spikePart_le α s t ht)

#print axioms norm_qResIntegrand_le

end RHFormalization
