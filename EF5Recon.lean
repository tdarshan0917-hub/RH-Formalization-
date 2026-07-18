import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.EnvelopeFromZeroDensity
import RHFormalization.ZpoleFromSeries

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

-- Current EF4 theorem.
#check Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
#print Harch_holomorphic_from_tsumPrincipalParts_and_Bregular

-- The V9 zero-density constructor chain.
#check buildEnvelopeFromZeroDensity
#check buildZeroPoleLUCAPIFromEnvelope
#check ZpoleSeries
#check defaultZeroMultiplicityData
#check defaultZeroExhaustion

-- Current V9 capstone.
#check RH_from_designed_D_zero_density
#print RH_from_designed_D_zero_density

-- Principal-part bridge pieces from EF4.
#check designedY_BPP_pair_from_tsum
#check zside_pair_principalPart_from_convergence
#check pairGroupedPoleClass
#check groupedResidueCoeff

end

end RHFormalization
