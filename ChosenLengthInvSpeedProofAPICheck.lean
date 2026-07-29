import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFR
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeExplicitRate
import RHFormalization.PrimePowerMassEnvelope
import Mathlib.Topology.Algebra.Order

namespace RHFormalization

variable (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)

#check buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFR
#check chosenLengthWindowAPI_of_invSpeed

#check S.sharpSpeed.toCompactSpeedAPI.speed
#check sharpCutoffConcreteChosenSpeed_speed_eq
#check S.hL_chosen
#check S.massEnvelopeData
#print PrimePowerMassEnvelopeData

-- likely nonnegativity fields; some may fail, that is fine
#check S.massEnvelopeData.h_massEnvelope_nonneg
#check S.massEnvelopeData.h_nonneg
#check S.massEnvelopeData.massEnvelope_nonneg
#check S.massEnvelopeData.h_mass_nonneg

-- speed denominator data
#check S.sharpSpeed.h_Gbound_nonneg
#check S.sharpSpeed.h_compactRadius_nonneg
#check S.sharpSpeed.hL_pos

-- common asymptotic / eventually helpers
#check Filter.eventually_ge_atTop
#check tendsto_inverse_atTop_zero
#check tendsto_one_div_atTop_nhds_zero_nat
#check tendsto_const_nhds
#check Filter.Tendsto.const_mul

end RHFormalization
