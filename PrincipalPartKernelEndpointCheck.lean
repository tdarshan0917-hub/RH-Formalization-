import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.BsharedPrincipalPartAtWitness
import RHFormalization.ExplicitFormulaHolomorphyFromTsum

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

#check RH_from_designed_D_zero_density_localEF_noBregular
#check designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
#check designedY_BPP_pair_from_tsum
#check designedY_Cshared_Bshared_eq_tsum_global
#check displacementCanonicalKernel
#check HasPrincipalPartAtC

-- Exact hard theorem we now need:
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
  RH_from_designed_D_zero_density_localEF_noBregular
    (by
      intro s hs_im hs_re_pos hs_re_lt
      exact zeta_not_locally_zero s) -- this line may fail; it is only probing the endpoint shape
    sorry
    h_tsum_principalPart
    sorry

end

end RHFormalization
