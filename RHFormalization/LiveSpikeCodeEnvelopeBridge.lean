import RHFormalization.SpikeEnvelopeUniformBound
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators
variable {N : ℕ}

/-- **Live spike sum uniformly bounded (cutoff-independent).** For any finite set
`I` of prime-power pairs and `t > 0`, the weighted heat-kernel envelope sum over
`I` is ≤ the tsum over ALL prime-power pairs — a single constant independent of
`I` (hence of the admissible cutoff stage). This is the reindexed, live-weight
form of `spike_envelope_sum_le_tsum`: the bound the R_stage estimate needs, with
the uniformity coming from absolute summability (partial ≤ total). -/
theorem live_spike_envelope_uniform_bound
    (t : ℝ) (ht : 0 < t) (I : Finset PrimePowerPair) :
    ∑ q ∈ I, heatKernelWeightedEnvelope t q
      ≤ ∑' q : PrimePowerPair, heatKernelWeightedEnvelope t q :=
  spike_envelope_sum_le_tsum t ht I

/-- The uniform bound as an explicit constant: name the tsum as the cutoff-free
envelope constant `C_env(t)`. -/
noncomputable def spikeEnvelopeConst (t : ℝ) : ℝ :=
  ∑' q : PrimePowerPair, heatKernelWeightedEnvelope t q

theorem live_spike_le_const
    (t : ℝ) (ht : 0 < t) (I : Finset PrimePowerPair) :
    ∑ q ∈ I, heatKernelWeightedEnvelope t q ≤ spikeEnvelopeConst t := by
  unfold spikeEnvelopeConst
  exact spike_envelope_sum_le_tsum t ht I

#print axioms live_spike_envelope_uniform_bound
#print axioms live_spike_le_const
end RHFormalization
