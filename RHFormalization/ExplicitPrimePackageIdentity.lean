import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.CanonicalPrimePowerTsumPrincipalPart

/-!
# RHFormalization.ExplicitPrimePackageIdentity

Reusable explicit-formula bridge.

The designed shared canonical package is definitionally the concrete prime-power
tsum package. This file does not create a new RH endpoint. It prepares the
explicit-formula campaign by making the prime side fully concrete.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The designed shared canonical package is definitionally the concrete
prime-power tsum package.
-/
theorem designedY_Cshared_eq_concreteTsumPackage :
    designedY.B.Cshared =
      canonicalPrimePowerPackageFromKernelTsum
        designedY.B.Cshared.sigma0
        (displacementCanonicalKernel (heatKernelG 1)) := by
  rfl

/--
Global, hypothesis-free version of the designed prime-side identity.
-/
theorem designedY_Cshared_Bshared_eq_tsum_global
    (s : ℂ) :
    designedY.B.Cshared.Bshared s =
      ∑' q : PrimePowerPair,
        q.weightC *
          (displacementCanonicalKernel (heatKernelG 1)) q.center s := by
  rfl

/--
If the concrete prime-power tsum has the required opposite principal parts at
all zero witnesses, then the designed shared package has the B-side
opposite-principal-part data needed by the local cancellation bridge.
-/
def designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
    (M : ZeroMultiplicityData)
    (groupedClass :
      ∀ W : ZeroWitness, GroupedPoleClass M W)
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC *
                (displacementCanonicalKernel (heatKernelG 1)) q.center s)
          W.s0
          (-(groupedResidueCoeff M (groupedClass W)))) :
    BsharedOppositePrincipalPartData designedY M :=
  BsharedOppositePrincipalPartData_of_tsum_principalParts
    designedY
    designedY.B.Cshared.sigma0
    (displacementCanonicalKernel (heatKernelG 1))
    M
    groupedClass
    designedY_Cshared_eq_concreteTsumPackage
    h_tsum_principalPart

#print axioms designedY_Cshared_eq_concreteTsumPackage
#print axioms designedY_Cshared_Bshared_eq_tsum_global
#print axioms designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts

end

end RHFormalization
