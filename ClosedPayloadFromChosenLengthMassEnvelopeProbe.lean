import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget

namespace RHFormalization

variable (X : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X)

#check S.alpha
#check S.Lstage
#check S.h_R_ge_nat
#check S.h_indices_contains_of_center_le_R
#check S.h_indices_subset_center_le_R
#check S.h_coordSet_compact
#check S.h_coord_mem
#check S.hL_chosen

#print CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
#print CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload

-- These are the key fields we need to see whether S already contains:
#check S.sharpSpeed
#check S.kernelID
#check S.coordSet
#check S.massEnum
#check S.massEnvelopeData

end RHFormalization
