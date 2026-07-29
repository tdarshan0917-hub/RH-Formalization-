import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.ShiftedLaplaceWitnessCancellationFromPrincipalParts
import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.DesignedDetailedConstruction

namespace RHFormalization

#check shiftedLaplacePrimePackageAt
#check designedY.B.Cshared
#check shiftedLaplacePrimePackageAt 0

#check designedY_Cshared_sigma0
#check designedY_Cshared_Bshared_eq_tsum_global
#check shiftedLaplacePrimePackageAt

-- Try definitional comparison at sigma0 = 0
#check (shiftedLaplacePrimePackageAt 0).Bshared
#check designedY.B.Cshared.Bshared

-- Candidate regularity mismatch check
#check designedY_Bshared_regular

-- Cancellation constructors
#check shiftedLaplace_hcancel_from_grouped_principalParts
#check shiftedLaplaceWitnessCancellationData_from_opposite_principalParts

end RHFormalization
