import RHFormalization.ShiftedLaplaceDSharedBridge
import RHFormalization.AppendixDOperatorPrimePowerDetailedConstruction
import RHFormalization.AppendixDOperatorFiniteCanonicalDetailedConstruction
import RHFormalization.AppendixDPrimePowerLimitReduction
import RHFormalization.DOperatorExport
import RHFormalization.DesignedDetailedConstruction
import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.CurrentFrontierEndpoint

/-!
# ShiftedLaplaceYBuilderAudit2

Scratch audit only. Do not import.

This fixes the previous bad name guesses and asks the real question:

Can the shifted-Laplace shared package be promoted through existing D/Y
constructors without editing old D files?
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

-- Green shifted bridge.
#check shiftedLaplacePrimePackageAt
#check shiftedLaplace_DBcan_from_actualKernelError_matches_shared
#check shiftedLaplace_DBcan_from_asymptoticKernel_matches_shared

-- Correct D/Y builder names.
#check buildDDetailedConstructionWithOperatorLegalityFromPrimePowerLimit
#check buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
#check buildDDetailedConstructionWithOperatorLegalityFromRCutoffEstimate

-- Exact data required by the two relevant routes.
#print DOperatorPrimePowerLimitAtOverlapData
#print DOperatorFiniteCanonicalLimitAtOverlapData
#print DOverlapIdentityAPI

-- The existing designed object fields we might reuse only if the overlap obligation permits it.
#check designedY
#check designedY.finiteOperatorLayer
#check designedY.W
#check designedY.Wapi
#check designedY.B
#check designedY.F
#check designedY.sectors
#check designedY.sectorSplit
#check designedY.sectorBounds
#check designedY.master
#check designedY.overlapBuilder

-- Final spines. We want a parallel theorem, not edits to CurrentFrontierEndpoint.
#check RH_current_frontier
#check finalRHSpine_from_Cshared_eq
#check finalRHSpine_from_HChosenDSharedC
#check RH_from_eta_zeroDensity_holo

end

end RHFormalization
