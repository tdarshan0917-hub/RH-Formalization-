import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability
import Mathlib.Analysis.PSeries

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

example :
    Summable heatKernelNatValueMajorant := by
  unfold heatKernelNatValueMajorant
  show
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ * ((q.natValue : ℝ) ^ 3)⁻¹)
  -- This is the live theorem. Work here.
  -- The next proof step is to compare this to a summable p-series/geometric majorant.

end

end RHFormalization
