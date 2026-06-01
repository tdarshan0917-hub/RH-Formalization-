import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummability

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

example
    (t : ℝ)
    (ht : 0 < t) :
    Summable (heatKernelExplicitWeightedEnvelope t) := by
  unfold heatKernelExplicitWeightedEnvelope
  show
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ *
          ((1 : ℝ) / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-(q.center ^ 2) / (4 * t))))
  -- The proof starts here. No `sorry`.

end

end RHFormalization
