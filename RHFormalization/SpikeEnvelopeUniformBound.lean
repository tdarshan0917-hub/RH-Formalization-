import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityClosure
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import Mathlib

/-!
# Cutoff-uniform spike-sum bound via summability (the missing uniformity).

The per-stage spike sum runs over a FINITE subset of PrimePowerPair that GROWS with
the cutoff. The full prime-power heat-kernel envelope series is SUMMABLE
(heatKernelWeightedEnvelope_summable). Therefore every stage's partial spike sum is
≤ the tsum over ALL prime powers — a single constant independent of the stage.

This is the cutoff-uniformity the all-Ω residual bound needs: not from cancellation,
but from absolute summability of the prime-power heat envelope. partial ≤ total.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- **Cutoff-uniform spike envelope bound.** For any finite set `I` of prime-power pairs
and `t > 0`, the spike-envelope sum over `I` is bounded by the tsum over ALL pairs,
a constant independent of `I` (hence of the cutoff stage). -/
theorem spike_envelope_sum_le_tsum
    (t : ℝ) (ht : 0 < t) (I : Finset PrimePowerPair) :
    ∑ q ∈ I, heatKernelWeightedEnvelope t q
      ≤ ∑' q : PrimePowerPair, heatKernelWeightedEnvelope t q := by
  have hsummable := heatKernelWeightedEnvelope_summable t ht
  refine hsummable.sum_le_tsum I (fun q _ => ?_)
  -- envelope nonneg: ‖weightC‖ · ‖heatKernelG‖ ≥ 0
  rw [heatKernelWeightedEnvelope_apply]
  positivity

#print axioms spike_envelope_sum_le_tsum

end RHFormalization
