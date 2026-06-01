import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummability

Concrete summability target for the heat-kernel weighted prime-power series.

This file only exposes the explicit Gaussian-weighted envelope and the bridge
from explicit-envelope summability to heat-kernel-envelope summability.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The explicit real Gaussian-weighted prime-power envelope.
-/
noncomputable def heatKernelExplicitWeightedEnvelope
    (t : ℝ) :
    PrimePowerPair → ℝ :=
  fun q : PrimePowerPair =>
    ‖q.weightC‖ *
      ((1 : ℝ) / Real.sqrt (4 * Real.pi * t) *
        Real.exp (-(q.center ^ 2) / (4 * t)))

/--
For positive heat time, the heat-kernel weighted envelope is pointwise equal
to the explicit Gaussian-weighted envelope.
-/
theorem heatKernelWeightedEnvelope_eq_explicit
    (t : ℝ)
    (ht : 0 < t) :
    heatKernelWeightedEnvelope t =
      heatKernelExplicitWeightedEnvelope t := by
  funext q
  exact heatKernelWeightedEnvelope_apply_expanded t ht q

/--
If the explicit Gaussian-weighted prime-power envelope is summable, then the
heat-kernel weighted envelope is summable.
-/
theorem heatKernelWeightedEnvelope_summable_of_explicit
    (t : ℝ)
    (ht : 0 < t)
    (h_explicit :
      Summable (heatKernelExplicitWeightedEnvelope t)) :
    Summable (heatKernelWeightedEnvelope t) := by
  simpa [heatKernelWeightedEnvelope_eq_explicit t ht] using h_explicit

end

end RHFormalization
