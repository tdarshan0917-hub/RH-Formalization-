import RHFormalization.ShiftedLaplaceBsharedMeromorphicFromIdentity
import RHFormalization.ShiftedLaplaceLogDerivIdentity
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- Bshared agrees with the closed form on the deep half-plane. -/
theorem shiftedLaplace_Bshared_eq_closedForm
    {s : ℂ} (hw : 1 < (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)).re) :
    shiftedLaplacePrimePackage.Bshared s = shiftedClosedForm s := by
  rw [shiftedLaplace_Bshared_eq_logDeriv hw]
  rfl

#print axioms shiftedLaplace_Bshared_eq_closedForm

end
end RHFormalization
