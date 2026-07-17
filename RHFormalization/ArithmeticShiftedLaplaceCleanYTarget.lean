import RHFormalization.ArithmeticShiftedLaplaceIntegratedManifest

/-!
# ArithmeticShiftedLaplaceCleanYTarget

Safe EFH plug target.

The full EFH spine needs a `Y : DDetailedConstructionWithOperatorLegality`.

We already have the clean DBcan object:

  arithmeticShiftedLaplaceCleanDBcanLimitSigma1

But directly stating `Y.B = arithmeticShiftedLaplaceCleanDBcanLimitSigma1`
is dependent-type unsafe unless we also prove the finite operator layers are
definitionally/equationally aligned.

So this file records the usable EFH plug condition instead:

  Y.B.Cshared = arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Cshared

Since the clean DBcan's Cshared is definitionally:

  shiftedLaplaceModelPackageAt 1

this gives the exact Cshared identity needed by Appendix E / H / F.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators Classical

/--
If a full D-side `Y` has the same shared canonical package as the clean
shifted-Laplace DBcan object, then its Cshared is the shifted-Laplace model
package at σ = 1.
-/
theorem cleanY_Cshared_eq_model_of_Cshared_eq_cleanDBcan
    (Y : DDetailedConstructionWithOperatorLegality)
    (hC :
      Y.B.Cshared =
        arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Cshared) :
    Y.B.Cshared = shiftedLaplaceModelPackageAt 1 := by
  rw [hC]
  rfl

/--
Same identity in the opposite orientation.
-/
theorem cleanY_model_eq_Cshared_of_Cshared_eq_cleanDBcan
    (Y : DDetailedConstructionWithOperatorLegality)
    (hC :
      Y.B.Cshared =
        arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Cshared) :
    shiftedLaplaceModelPackageAt 1 = Y.B.Cshared := by
  exact (cleanY_Cshared_eq_model_of_Cshared_eq_cleanDBcan Y hC).symm

/--
Functional Bshared identity following from the clean Cshared identification.
This is the form Appendix-E functional compatibility uses.
-/
theorem cleanY_sharedBIdentity_of_Cshared_eq_cleanDBcan
    (Y : DDetailedConstructionWithOperatorLegality)
    (hC :
      Y.B.Cshared =
        arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Cshared) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane Y.B.Cshared.sigma0 →
        Y.B.Cshared.Bshared s =
          (shiftedLaplaceModelPackageAt 1).Bshared s := by
  intro s hs
  have hmodel := cleanY_Cshared_eq_model_of_Cshared_eq_cleanDBcan Y hC
  rw [hmodel]

/--
The honest remaining plug target.

To enter EFH cleanly, we need a full `Y` plus proof that its shared canonical
package agrees with the clean shifted-Laplace DBcan package.

This avoids the dependent-type trap of asserting whole-record equality
`Y.B = arithmeticShiftedLaplaceCleanDBcanLimitSigma1`.
-/
structure ArithmeticShiftedLaplaceCleanYPlugTarget where
  Y : DDetailedConstructionWithOperatorLegality
  h_Cshared_clean :
    Y.B.Cshared =
      arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Cshared
  h_Bcan_clean_on_overlap :
    ∀ s : ℂ,
      s ∈ RightHalfPlane Y.finiteOperatorLayer.toStagePackage.sigma0 →
        Y.B.Bcan s =
          arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Bcan s

/--
Any clean-Y plug target gives the Cshared identity needed by the EFH spine.
-/
theorem ArithmeticShiftedLaplaceCleanYPlugTarget.Cshared_eq_model
    (T : ArithmeticShiftedLaplaceCleanYPlugTarget) :
    T.Y.B.Cshared = shiftedLaplaceModelPackageAt 1 :=
  cleanY_Cshared_eq_model_of_Cshared_eq_cleanDBcan
    T.Y T.h_Cshared_clean

/--
Any clean-Y plug target gives the functional Bshared identity needed by
Appendix-E compatibility.
-/
theorem ArithmeticShiftedLaplaceCleanYPlugTarget.sharedBIdentity
    (T : ArithmeticShiftedLaplaceCleanYPlugTarget) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane T.Y.B.Cshared.sigma0 →
        T.Y.B.Cshared.Bshared s =
          (shiftedLaplaceModelPackageAt 1).Bshared s :=
  cleanY_sharedBIdentity_of_Cshared_eq_cleanDBcan
    T.Y T.h_Cshared_clean

#print axioms cleanY_Cshared_eq_model_of_Cshared_eq_cleanDBcan
#print axioms cleanY_model_eq_Cshared_of_Cshared_eq_cleanDBcan
#print axioms cleanY_sharedBIdentity_of_Cshared_eq_cleanDBcan
#print axioms ArithmeticShiftedLaplaceCleanYPlugTarget
#print axioms ArithmeticShiftedLaplaceCleanYPlugTarget.Cshared_eq_model
#print axioms ArithmeticShiftedLaplaceCleanYPlugTarget.sharedBIdentity

end

end RHFormalization
