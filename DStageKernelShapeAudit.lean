import RHFormalization.ShiftedLaplaceDSharedBridge
import RHFormalization.DesignedDetailedConstruction
import RHFormalization.AppendixDPrimePowerFiniteFormulaTarget
import RHFormalization.AppendixDFiniteSpikeExtractionWitness
import RHFormalization.CanonicalPrimePowerConcreteTsumPackage
import RHFormalization.ExplicitPrimePackageIdentity

/-!
# DStageKernelShapeAudit

Scratch audit only. Do not import this file.

Question:
Is the finite canonical D-stage kernel already the shifted/Laplace/Stieltjes
kernel, or is it still the displacement heat kernel?

This decides whether the shifted-Laplace package can be carried by existing
D finite-canonical limit machinery, or whether the missing theorem is the
Appendix-D transform passage.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

-- Existing designed D-side package.
#check designedY
#check designedY.finiteOperatorLayer
#check designedY.finiteOperatorLayer.toFiniteCanonicalPrimePowerFormula
#check designedY.finiteOperatorLayer.toFiniteCanonicalPrimePowerFormula.kernel
#check designedY.finiteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices

-- Existing old Bshared identification.
#check designedY_Cshared_Bshared_eq_tsum_global
#print displacementCanonicalKernel
#print heatKernelG

-- New shifted package.
#check shiftedLaplaceHeatKernelC
#check shiftedLaplacePrimePackageAt
#print shiftedLaplaceHeatKernelC

-- Finite canonical package constructor and formula structures.
#check finiteCanonicalPrimePowerPackage
#print DFiniteCanonicalPrimePowerFormula
#print DFiniteStagePackageFromOperatorLayer

-- Current D finite-stage formula target names.
#check DOperatorFiniteCanonicalLimitAtOverlapData
#check buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit

end

end RHFormalization
