import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromLimits
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualConcrete
import RHFormalization.DOperatorExport
import RHFormalization.HalfPlaneGeometry

namespace RHFormalization

#check buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthLimits

-- Remaining payload shape.
#check HolomorphicOnC
#check Ω
#check DFiniteStagePackageFromOperatorLayer
#check DFiniteStagePackage
#check DFiniteStagePackageFromOperatorLayer.toStagePackage

-- Existing generic constructors / fields.
#check buildDFHLimitDataFromCompactUniform
#check buildDMasterResidualDataFromCompactUniform

#print DFHLimitData
#print DMasterResidualData

-- Geometry / sigma candidates.
#check rightHalfPlane_subset_Omega
#check buildOverlapGeometryFromSigmaNonnegative

end RHFormalization
