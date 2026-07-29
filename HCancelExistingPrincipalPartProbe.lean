import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.CanonicalPrimePowerTsumPrincipalPart
import RHFormalization.BsharedPrincipalPartAtWitness
import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts
import RHFormalization.ExplicitFormulaLocalReduction

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check HasPrincipalPartAtC
#check BsharedOppositePrincipalPartData
#check Harch_witness_extensions_from_BsharedPrincipalPartData
#check canonicalPrimePowerPackageFromKernelTsum_oppositePrincipalPart_at_witness
#check BsharedOppositePrincipalPartData_of_tsum_principalParts
#check Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
#check shiftedLaplacePrimePackageAt
#check shiftedLaplacePrimePackageAt_Bshared_eq_tsum
#check ShiftedLaplaceWitnessCancellationData
#check WitnessCancellationData

/-
Real target:

∀ W : ZeroWitness,
  ShiftedLaplaceWitnessCancellationData sigma0 W

We are checking whether the existing canonical-prime-power principal-part theorem
can be specialized to:

  canonicalPrimePowerPackageFromKernelTsum sigma0 shiftedLaplaceHeatKernelC

which is definitionally shiftedLaplacePrimePackageAt sigma0.
-/

example (sigma0 : ℝ) :
    shiftedLaplacePrimePackageAt sigma0 =
      canonicalPrimePowerPackageFromKernelTsum sigma0 shiftedLaplaceHeatKernelC := by
  rfl

end

end RHFormalization
