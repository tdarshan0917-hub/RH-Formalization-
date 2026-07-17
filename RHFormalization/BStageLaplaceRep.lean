import RHFormalization.BSideHeatKernelLaplace
import RHFormalization.ArithmeticPrimeShiftedLaplaceBStage
import Mathlib

/-!
# B-stage Laplace representation (D.A2 twin, full).

Lifts the per-spike B-side connector to the full finite spike sum:
the B-stage equals the Laplace transform of the summed shifted heat spikes.

  arithmeticShiftedLaplaceBStage α s = ∫₀^∞ e^{-st} (∑ spikes·exp(-t/4)·heatKernelG t aᵢ) dt

Built on the single named connector shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG;
no new analytic content, just the finite-sum lift (Finset.sum of the connector).
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- The summed B-side time integrand: ∑ over active spikes of weight·shiftedHeatIntegrand. -/
noncomputable def bStageHeatIntegrand (α : DFiniteStage) (s : ℂ) (t : ℝ) : ℂ :=
  ∑ q ∈ α.diagonalSpikeActiveIndices,
    α.diagonalSpikeContribution q *
      shiftedHeatIntegrand (PrimePowerPair.center (α.diagonalSpikeToPP q)) s t

#check @arithmeticShiftedLaplaceBStage
#check @bStageHeatIntegrand

end RHFormalization
