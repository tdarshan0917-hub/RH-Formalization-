import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

namespace RHFormalization

variable (X : DFiniteStagePackageFromOperatorLayer)
variable (t : ℝ)
variable (ht_pos : 0 < t)

-- This is the exact target we need next.
#check CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
#check buildCanonicalPrimePowerSharpCutoffHeatKernelWeightedDataFromClosedPayload

-- This is the likely upstream object carrying most H0 fields.
#check CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
#print CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData

-- This is the exact heat-kernel H0 package target.
#check CanonicalPrimePowerSharpCutoffHeatKernelWeightedData
#print CanonicalPrimePowerSharpCutoffHeatKernelWeightedData

end RHFormalization
