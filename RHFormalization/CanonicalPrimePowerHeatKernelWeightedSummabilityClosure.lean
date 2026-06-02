import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreSummability
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCore
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityClosure

Final closure of the heat-kernel weighted summability branch.

This file consumes the already-proved Gaussian-core summability theorem and
the existing bridge lemmas:
* `heatKernelExplicitWeightedEnvelope_summable_of_core`
* `heatKernelWeightedEnvelope_summable_of_core`
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The explicit weighted heat-kernel envelope is summable.
-/
theorem heatKernelExplicitWeightedEnvelope_summable
    (t : ℝ)
    (ht : 0 < t) :
    Summable (heatKernelExplicitWeightedEnvelope t) := by
  exact
    heatKernelExplicitWeightedEnvelope_summable_of_core
      t
      (heatKernelGaussianCoreEnvelope_summable t ht)

/--
The heat-kernel weighted envelope is summable.
-/
theorem heatKernelWeightedEnvelope_summable
    (t : ℝ)
    (ht : 0 < t) :
    Summable (heatKernelWeightedEnvelope t) := by
  exact
    heatKernelWeightedEnvelope_summable_of_core
      t
      ht
      (heatKernelGaussianCoreEnvelope_summable t ht)

end

end RHFormalization
