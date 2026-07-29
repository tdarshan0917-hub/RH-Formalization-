import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.CanonicalPrimePowerTsumPrincipalPart
import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

#check canonicalPrimePowerPackageFromKernelTsum
#check designedY.B.Cshared
#check designedY_Cshared_Bshared_eq_tsum
#check BsharedOppositePrincipalPartData_of_tsum_principalParts
#check Harch_holomorphic_from_principalParts_and_regular
#check Harch_witness_extensions_from_BsharedPrincipalPartData

/-
Probe 1:
Is the designed shared package globally definitionally equal to the concrete
tsum package with the same sigma?
-/
example :
    designedY.B.Cshared =
      canonicalPrimePowerPackageFromKernelTsum
        designedY.B.Cshared.sigma0
        (displacementCanonicalKernel (heatKernelG 1)) := by
  rfl

/-
Probe 2:
If the structure equality fails, is the Bshared field at least globally
definitionally equal?
-/
example (s : ℂ) :
    designedY.B.Cshared.Bshared s =
      (canonicalPrimePowerPackageFromKernelTsum
        designedY.B.Cshared.sigma0
        (displacementCanonicalKernel (heatKernelG 1))).Bshared s := by
  rfl

/-
Probe 3:
If both fail, does the explicit prime-power tsum equality hold globally by rfl?
We already know the overlap theorem exists; this tests whether it is stronger
definitionally.
-/
example (s : ℂ) :
    designedY.B.Cshared.Bshared s =
      ∑' q : PrimePowerPair,
        q.weightC *
          (displacementCanonicalKernel (heatKernelG 1)) q.center s := by
  rfl

end

end RHFormalization
