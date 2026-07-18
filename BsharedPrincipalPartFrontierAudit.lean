import RHFormalization.PrimeSideOperatorBridgeBLocalEF
import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.BsharedPrincipalPartAtWitness

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

-- Current strongest Bshared/local-EF endpoint.
#check RH_from_designed_D_zero_density_localEF_noBregular

-- The exact remaining hard input.
#check designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
#check designedY_BPP_pair_from_tsum

-- Z-side principal part is already available from convergence.
#check zside_pair_principalPart_from_convergence

-- Bshared regularity is already available.
#check designedY_Bshared_regular
#check designedY_Bshared_holomorphicAt

-- Global holomorphy assembly from tsum principal parts.
#check Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
#check designed_h_holo_from_localEF

-- Concrete tsum identity connecting designedY.B.Cshared.Bshared to the prime package.
#check designedY_Cshared_eq_concreteTsumPackage
#check designedY_Cshared_Bshared_eq_tsum_global

end

end RHFormalization
