import RHFormalization.PrimeSideOperatorBridgeBLocalEF
import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.ExplicitFormulaHolomorphyFromTsum

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

-- Green D.B endpoint.
#check RH_from_operatorBridgeB_localEF

-- Existing Bshared witness/principal-part machinery.
#check Harch_local_extension_at_witness_from_cancelled_principal_parts
#check Harch_witness_extensions_from_Bshared_opposite_principalParts
#check Harch_holomorphic_from_principalParts_and_regular
#check designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
#check designedY_Bshared_regular
#check designedY_Bshared_holomorphicAt

-- Existing strong Bshared endpoint.
#check RH_from_designed_D_zero_density_localEF_noBregular

-- D.B / Bshared overlap bridge.
#check designedY_Cshared_Bshared_eq_operatorBridge_B_on_overlap
#check RH_from_operatorBridgeB_localEF

-- Constructor for the D.B contract: note what it requires.
#check primeSideAlignmentContract_of_D_B

end

end RHFormalization
