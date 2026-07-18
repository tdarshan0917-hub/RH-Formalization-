import RHFormalization.TwoInputEndpointFromEta
import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.DesignedDetailedConstruction

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check RH_from_eta_zeroDensity_holo
#check designed_Bshared_const
#check designedY_Cshared_Bshared_eq_tsum_global
#check designedY.toOperatorResolventBridge.B
#check designedY.toOperatorResolventBridge.FH

#print CanonicalKernelC
#print displacementCanonicalKernel

/--
Guardrail theorem: the current designed Bshared is constant in the complex
variable because the current kernel ignores s.
-/
theorem current_designedY_Bshared_constant_in_s (s t : ℂ) :
    designedY.B.Cshared.Bshared s =
      designedY.B.Cshared.Bshared t := by
  rw [designedY_Cshared_Bshared_eq_tsum_global s]
  rw [designedY_Cshared_Bshared_eq_tsum_global t]
  simp [displacementCanonicalKernel]

#print axioms current_designedY_Bshared_constant_in_s

end

end RHFormalization
