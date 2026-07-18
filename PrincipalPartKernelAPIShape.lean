import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.BsharedPrincipalPartAtWitness
import RHFormalization.ExplicitFormulaHolomorphyFromTsum

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

#check displacementCanonicalKernel
#check heatKernelG
#check PrimePowerPair
#check groupedResidueCoeff
#check pairGroupedPoleClass
#check HasPrincipalPartAtC
#check designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
#check designedY_BPP_pair_from_tsum
#check designedY_Cshared_Bshared_eq_tsum_global
#check RH_from_designed_D_zero_density_localEF_noBregular

-- Exact missing target shape:
#check fun
  (h_tsum_principalPart :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s : ℂ =>
          ∑' q : PrimePowerPair,
            q.weightC * displacementCanonicalKernel (heatKernelG 1) q.center s)
        W.s0
        (-(groupedResidueCoeff
            defaultZeroMultiplicityData
            (pairGroupedPoleClass defaultZeroMultiplicityData W)))) =>
  h_tsum_principalPart

end

end RHFormalization
