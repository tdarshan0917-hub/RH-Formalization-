import RHFormalization.QResNormBound
import RHFormalization.BStageLaplaceRep
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import Mathlib

/-!
# Spike-part norm bound (Leaf 2, rung 2).

‖bStageHeatIntegrand α s t‖
  ≤ ∑_q |contribution q| · e^{-Re(s)·t} · e^{-t/4} · heatKernelRealScalar t (center q)

via norm_sum_le + norm_mul + norm_exp + norm_heatKernelG_eq_realScalar (for t > 0).
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- **Pointwise spike-part norm bound.** -/
theorem norm_spikePart_le
    (α : DFiniteStage) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖bStageHeatIntegrand α s t‖
      ≤ ∑ q ∈ α.diagonalSpikeActiveIndices,
          ‖α.diagonalSpikeContribution q‖ *
            (Real.exp (-s.re * t) * Real.exp (-t/4) *
              heatKernelRealScalar t (PrimePowerPair.center (α.diagonalSpikeToPP q))) := by
  unfold bStageHeatIntegrand shiftedHeatIntegrand
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro q _
  rw [norm_mul, norm_mul, norm_mul]
  rw [norm_heatKernelG_eq_realScalar _ _ ht]
  -- ‖contribution‖ · ‖e^{-s t}‖ · ‖e^{-t/4}‖ · heatKernelRealScalar
  have he1 : ‖Complex.exp (-s * (t:ℂ))‖ = Real.exp (-s.re * t) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  have he2 : ‖Complex.exp (-(t:ℂ)/4)‖ = Real.exp (-t/4) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.div_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [he1, he2]

#print axioms norm_spikePart_le

end RHFormalization
