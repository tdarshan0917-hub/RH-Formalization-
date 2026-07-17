import RHFormalization.BStageLaplaceRep
import RHFormalization.DA2HeatTrace
import Mathlib
import RHFormalization.BSideHeatKernelLaplaceConnector

/-!
# B-stage = Laplace transform of summed heat spikes (sum-lift of the named connector).

arithmeticShiftedLaplaceBStage α s = ∫₀^∞ bStageHeatIntegrand α s t dt.

Pure finite-sum lift of shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG:
each spike kernel = its Laplace integral (the connector), sum over active spikes,
swap finite sum and integral. No new analytic content beyond the named connector.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- **B-stage Laplace representation.** The shifted-Laplace B-stage equals the
Laplace transform of the summed shifted heat spikes. Sum-lift of the named connector. -/
theorem arithmeticShiftedLaplaceBStage_eq_laplace
    (α : DFiniteStage) (s : ℂ) (hs : 0 < s.re)
    (hcenter : ∀ q ∈ α.diagonalSpikeActiveIndices,
      0 ≤ PrimePowerPair.center (α.diagonalSpikeToPP q))
    (hint : ∀ q ∈ α.diagonalSpikeActiveIndices,
      MeasureTheory.IntegrableOn
        (fun t => shiftedHeatIntegrand (PrimePowerPair.center (α.diagonalSpikeToPP q)) s t)
        (Set.Ioi 0)) :
    arithmeticShiftedLaplaceBStage α s
      = ∫ t in Set.Ioi (0:ℝ), bStageHeatIntegrand α s t := by
  rw [arithmeticShiftedLaplaceBStage_eq_finiteNatSpikePackage]
  unfold bStageHeatIntegrand
  rw [MeasureTheory.integral_finset_sum _ (by
    intro q hq
    exact (hint q hq).const_mul _)]
  -- LHS finiteNatSpikePackage = ∑ contribution·spikeKernel ; spikeKernel = shiftedLaplaceHeatKernelC center
  simp only [finiteNatSpikePackage, arithmeticShiftedLaplaceSpikeKernel]
  apply Finset.sum_congr rfl
  intro q hq
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane
    (PrimePowerPair.center (α.diagonalSpikeToPP q)) (hcenter q hq) s hs

#print axioms arithmeticShiftedLaplaceBStage_eq_laplace

end RHFormalization
