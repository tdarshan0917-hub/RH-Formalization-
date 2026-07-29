import RHFormalization.AppendixHOverlapFromLocalExtensions
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.ExplicitFormulaBRegular

namespace RHFormalization

open Complex Set Topology Filter Metric
open scoped BigOperators

#print displacementCanonicalKernel
#print heatKernelG

#check designedY_Cshared_Bshared_eq_tsum
#check designedY_Cshared_Bshared_eq_tsum_global
#check designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts

/--
If this example proves by simp, then the current explicit prime-side series
is independent of `s`. In that case it cannot supply nonzero principal parts,
and the next task is to locate the intended s-dependent transform kernel.
-/
example (s t : ℂ) :
    (∑' q : PrimePowerPair,
      q.weightC *
        (displacementCanonicalKernel (heatKernelG 1)) q.center s)
    =
    (∑' q : PrimePowerPair,
      q.weightC *
        (displacementCanonicalKernel (heatKernelG 1)) q.center t) := by
  simp [displacementCanonicalKernel]

end RHFormalization
