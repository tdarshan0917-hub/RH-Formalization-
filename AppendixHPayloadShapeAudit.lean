import RHFormalization.AppendixHZeroDensityInterfaceEndpoint
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.PrimeSideAlignmentToHarch
import RHFormalization.PrimeSideAlignmentDesignedBridge

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

-- Current new endpoint.
#check RH_from_appendixH_interface_zeroDensity

-- Existing D/V9 endpoints.
#check RH_from_designed_D_summable
#check RH_from_designed_D_zero_density
#check RH_from_designed_D_zero_density_localEF
#check RH_from_designed_D_zero_density_localEF_noBregular

-- H-architecture package and constructors.
#check HArchPackage
#check HArchPackage.mk

-- Known holomorphy / Harch builders from previous route.
#check Harch_holomorphic_from_principalParts_and_Bregular
#check Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
#check designed_h_holo_from_localEF

-- Known Bshared regularity/principal-part tools.
#check designedY_Bshared_regular
#check designedY_Bshared_holomorphicAt
#check designedY_BPP_pair_from_tsum
#check designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
#check zside_pair_principalPart_from_convergence

-- D/B overlap and aligned-Harch route.
#check designedY_Cshared_Bshared_eq_operatorBridge_B_on_overlap
#check alignedHarchPackage
#check alignedHarch_split_on_D_overlap
#check alignedHarch_split_for_Btarget_on_D_overlap

end

end RHFormalization
