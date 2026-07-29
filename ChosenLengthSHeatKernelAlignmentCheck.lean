import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

namespace RHFormalization

variable (X : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X)
variable (t : ℝ)
variable (ht_pos : 0 < t)

#check S.G
#check S.Kshared
#check heatKernelG t
#check displacementCanonicalKernel (heatKernelG t)

-- Test whether S is already heat-kernel specialized.
example : S.G = heatKernelG t := by
  rfl

example : S.Kshared = displacementCanonicalKernel (heatKernelG t) := by
  rfl

-- If these rfl tests pass, S can likely feed the closed payload directly.
-- If they fail, S is still generic and we need the heat-kernel-specific H0/closed-payload route.

end RHFormalization
