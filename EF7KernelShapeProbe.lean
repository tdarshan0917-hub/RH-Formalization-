import RHFormalization.ExplicitFormulaBRegular

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

-- Current strongest local-EF theorem.
#check RH_from_designed_D_zero_density_localEF_noBregular

-- Confirm the kernel shape.
#print displacementCanonicalKernel
#check displacementCanonicalKernel
#check heatKernelG

-- Confirm the remaining principal-part target.
#check HasPrincipalPartAtC
#check groupedResidueCoeff
#check pairGroupedPoleClass
#check groupedResidueCoeff_ne_zero

-- The crucial shape test:
-- is the current prime-side tsum definitionally constant in s?
example (s : ℂ) :
    (∑' q : PrimePowerPair,
      q.weightC *
        (displacementCanonicalKernel (heatKernelG 1)) q.center s)
    =
    (∑' q : PrimePowerPair,
      q.weightC * heatKernelG 1 q.center) := by
  simp [displacementCanonicalKernel]

end

end RHFormalization
