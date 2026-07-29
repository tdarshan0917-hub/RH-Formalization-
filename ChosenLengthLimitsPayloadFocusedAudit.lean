import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromLimits
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualConcrete
import RHFormalization.DOperatorExport
import RHFormalization.GlobalRigidity
import RHFormalization.HalfPlaneGeometry

namespace RHFormalization

#check buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthLimits

-- The target payload.
#check HolomorphicOnC
#check Ω

-- Generic F/R constructors.
#check buildDFHLimitDataFromCompactUniform
#check buildDMasterResidualDataFromCompactUniform

-- Existing structure fields.
#print DFHLimitData
#print DMasterResidualData

-- Geometry / sigma helpers.
#check rightHalfPlane_subset_Omega
#check buildOverlapGeometryFromSigmaNonnegative

end RHFormalization
