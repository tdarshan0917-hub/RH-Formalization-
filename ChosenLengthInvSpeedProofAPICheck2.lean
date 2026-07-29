import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFR
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeExplicitRate
import RHFormalization.CanonicalPrimePowerDWindowExactMassSpeedEstimate
import RHFormalization.CanonicalPrimePowerMassEnvelopeSpeedComparison
import Mathlib.Topology.Algebra.Order

namespace RHFormalization

variable (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)

#check buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFR
#check chosenLengthWindowAPI_of_invSpeed

#check S.sharpSpeed.toCompactSpeedAPI.speed
#check sharpCutoffConcreteChosenSpeed_speed_eq
#check S.hL_chosen
#check S.h_R_ge_nat
#check S.massEnvelopeData
#check S.massEnvelopeData.massEnvelope

-- Print the actual mass envelope structure and fields.
#check PrimePowerMassEnvelopeData
#print PrimePowerMassEnvelopeData

-- These may or may not exist; if one fails, use the printed structure above.
#check S.massEnvelopeData.h_massEnvelope_nonneg
#check S.massEnvelopeData.h_nonneg
#check S.massEnvelopeData.massEnvelope_nonneg
#check S.massEnvelopeData.h_mass_nonneg

-- Speed denominator data.
#check S.sharpSpeed.h_Gbound_nonneg
#check S.sharpSpeed.h_compactRadius_nonneg
#check S.sharpSpeed.hL_pos

-- Useful asymptotic/order helpers.
#check Filter.eventually_ge_atTop
#check tendsto_inverse_atTop_zero
#check tendsto_one_div_atTop_nhds_zero_nat
#check Filter.Tendsto.const_mul

-- Existing nearby theorem.
#check exactMass_div_speed_tendsto_zero_of_upper_lower

end RHFormalization
