import RHFormalization.RealPrimeRHSharp
import RHFormalization.RealPrimeRHClose
import RHFormalization.RealPrimeY
import RHFormalization.RealLayerDMasterProbe
import RHFormalization.RealOperatorStageData
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
REAL PRIME ENDGAME SURFACE.

This file intentionally does not touch:
  FinalRHAssembly
  hpoint
  clean shifted-Laplace DBcan
  model-corrected detours

The real-prime close is already banked as `realPrime_RH_sharp`.
This file freezes the exact working endpoint.
-/

#check realPrime_RH_sharp
#print axioms realPrime_RH_sharp

#check realPrime_RH
#print axioms realPrime_RH

#check realPrimeY
#print axioms realPrimeY

#check realLayerDMaster
#print axioms realLayerDMaster

#check RealOperatorStageData.h_F_stage_to_FHcan
#print axioms RealOperatorStageData.h_F_stage_to_FHcan

#check buildHonestYZeroResidualFromRealOperatorStageData
#print axioms buildHonestYZeroResidualFromRealOperatorStageData

end
end RHFormalization
