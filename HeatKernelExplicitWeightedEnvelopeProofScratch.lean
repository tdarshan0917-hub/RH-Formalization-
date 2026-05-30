import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummability

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

#check PrimePowerPair
#check PrimePowerPair.p
#check PrimePowerPair.m
#check PrimePowerPair.natValue
#check PrimePowerPair.center
#check PrimePowerPair.weightReal
#check PrimePowerPair.weightC
#check heatKernelExplicitWeightedEnvelope

/-
Target. Do not leave this as `sorry` in source.
Use this scratch file only to inspect the exact unfolding and theorem search.
-/
example
    (t : ℝ)
    (ht : 0 < t) :
    Summable (heatKernelExplicitWeightedEnvelope t) := by
  unfold heatKernelExplicitWeightedEnvelope
  -- Next proof obligation:
  -- prove summability over q : ℕ × ℕ of
  -- ‖q.weightC‖ *
  --   ((1 / sqrt (4πt)) * exp(-(q.center^2)/(4t)))
  --
  -- Do not package this. Prove it by comparison.
  fail_if_success exact inferInstance
  sorry

end

end RHFormalization
