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
  -- This is the real current goal.
  -- Do not paste Lean theorem text into zsh.
  -- Do not add another wrapper.
  -- We now need to prove summability of the explicit Gaussian-weighted envelope.
  show
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ *
          ((1 : ℝ) / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-(q.center ^ 2) / (4 * t))))
  -- STOP HERE: run Lean and send the resulting goal/error.
  -- No `sorry` in source.
