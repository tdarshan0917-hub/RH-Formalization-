import RHFormalization.TwoInputEndpointFromEta
import RHFormalization.ExplicitPrimePackageIdentity

/-!
# HoloModelAlignmentAudit

Scratch audit only. Do not import this file into `RHFormalization.lean`.

Purpose:
1. Confirm the current two-input endpoint.
2. Confirm the current `Bshared` is the displacement-kernel tsum.
3. Confirm the displacement-kernel tsum is constant in `s`.
4. Print the operator bridge objects so we can locate the true s-dependent
   Stieltjes/Laplace/resolvent B-side, if it exists.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check RH_from_eta_zeroDensity_holo
#check RH_from_designed_D_zero_density

#check designedY
#check designedY.toOperatorResolventBridge
#check designedY.toOperatorResolventBridge.FH
#check designedY.toOperatorResolventBridge.B
#check designedY.toOperatorResolventBridge.RH

#check designedY.B.Cshared.Bshared
#check designedY_Cshared_Bshared_eq_tsum_global
#print displacementCanonicalKernel
#print heatKernelG

/--
If this builds, then the current `designedY.B.Cshared.Bshared` is constant
in the complex variable. That means it is not the pole-producing transformed
prime-side object needed for the local principal-part cancellation proof.
-/
example (s t : ℂ) :
    designedY.B.Cshared.Bshared s =
      designedY.B.Cshared.Bshared t := by
  rw [designedY_Cshared_Bshared_eq_tsum_global s]
  rw [designedY_Cshared_Bshared_eq_tsum_global t]
  simp [displacementCanonicalKernel]

/--
Same fact directly at the concrete tsum level.
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

end

end RHFormalization
