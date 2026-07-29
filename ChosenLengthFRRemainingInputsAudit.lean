import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromFR
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualConcrete
import RHFormalization.HalfPlaneGeometry

namespace RHFormalization

variable (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)

#check buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthFR

-- Inspect fields likely usable for W/Wapi.
#check S.G
#check S.Lstage
#check S.alpha
#check S.sharpSpeed

-- Window data / API candidates.
#check sharpCutoffDCanonicalWindowData
#check DCanonicalWindowAPI
#print DCanonicalWindowAPI

-- F/R constructors still available.
#check buildDFHLimitDataFromCompactUniform
#check buildDMasterResidualDataFromCompactUniform

-- Geometry helper for hσ.
#check rightHalfPlane_subset_Omega
#check buildOverlapGeometryFromSigmaNonnegative

end RHFormalization
