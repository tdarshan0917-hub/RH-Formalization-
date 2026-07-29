import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceLogDerivIdentity

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter ArithmeticFunction
open scoped BigOperators

def shiftedLaplaceModelPackageAt (sigma0 : ℝ) : CanonicalPrimePowerPackage :=
  { Bshared := shiftedLaplaceLogDerivModel
    sigma0 := sigma0 }

theorem shiftedLaplaceModelPackageAt_Bshared_eq_model
    (sigma0 : ℝ) (s : ℂ) :
    (shiftedLaplaceModelPackageAt sigma0).Bshared s = shiftedLaplaceLogDerivModel s := rfl

theorem shiftedLaplaceModelPackageAt_Bmero (sigma0 : ℝ) :
    MeromorphicOn (fun s : ℂ => (shiftedLaplaceModelPackageAt sigma0).Bshared s) Ω := by
  simpa using shiftedLaplaceLogDerivModel_meromorphicOn_Omega

#print axioms shiftedLaplaceModelPackageAt_Bmero
end
end RHFormalization
