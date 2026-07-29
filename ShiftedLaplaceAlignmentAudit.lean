import RHFormalization.PrimeSideTransformKernelPrototype
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.CanonicalPrimePowerActualKernelError
import RHFormalization.CanonicalPrimePowerAsymptoticKernel
import RHFormalization.CanonicalPrimePowerConcreteTsumPackage
import RHFormalization.HSideOverlapChosenCshared
import RHFormalization.HMeromorphicLayerChosenCshared
import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.DesignedDetailedConstruction

/-!
# ShiftedLaplaceAlignmentAudit

Scratch audit only. Do not import this file.

Purpose:
1. Confirm the old designedY package is the displacement package.
2. Confirm the shifted Laplace package is a separate chosen package.
3. Print the exact H-side chosen-Cshared route.
4. Print the exact D-facing generic-kernel data needed if we later build a
   parallel shifted D package.

This is not editing D. This is deciding whether the existing package
infrastructure can carry the manuscript's shifted/Laplace kernel.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

-- Current endpoint package: old/displacement.
#check designedY_Cshared_Bshared_eq_tsum_global
#check designedY.B.Cshared
#check designedY.toOperatorResolventBridge
#print displacementCanonicalKernel

-- New prototype package: shifted/Laplace.
#check shiftedLaplaceHeatKernelC
#check shiftedLaplacePrimePackage
#check shiftedLaplacePrimePackage_Bshared_eq_tsum
#print shiftedLaplaceHeatKernelC
#print shiftedLaplacePrimePackage

-- H-side chosen-Cshared route. This should be H-only.
#check buildHSideOverlapPackageWithChosenCshared
#check buildHSideOverlapPackageWithChosenCshared_Cshared_eq
#check buildHMeromorphicPackageLayerWithChosenCshared
#check buildHMeromorphicPackageLayerWithChosenCshared_Cshared_eq
#check buildHMeromorphicWithNormalFormPolesWithChosenCshared
#check buildHMeromorphicWithNormalFormPolesWithChosenCshared_Cshared_eq

-- D-facing generic-kernel route. We are only printing fields/signatures.
#check canonicalPrimePowerPackageFromKernelTsum
#print CanonicalPrimePowerActualKernelErrorData
#print CanonicalPrimePowerAsymptoticKernelMajorantData

#check buildDBcanLimitDataFromCanonicalPrimePowerActualKernelError
#check canonicalPrimePowerActualKernelError_h_Bcan_matches_tsum

#check buildDBcanLimitDataFromCanonicalPrimePowerAsymptoticKernel
#check canonicalPrimePowerAsymptoticKernel_h_Bcan_matches_tsum

end

end RHFormalization
