import RHFormalization.ShiftedLaplaceModelExhaustionSigma1

/-!
# Shifted-Laplace D-side `DBcanLimitData` at σ = 1

Assembles the `DBcanLimitData` for the σ=1 shifted-Laplace operator layer with the
log-derivative model package, from the axiom-clean exhaustion data
`shiftedLaplaceModelExhaustionSigma1`.

This is the D-side `Bcan` limit object: its `Bcan` agrees with the model on the
overlap half-plane.
-/

namespace RHFormalization
noncomputable section
open Complex

/-- The D-side `Bcan` limit data for the σ=1 shifted-Laplace layer + model package. -/
def shiftedLaplaceDBcanLimitSigma1 :
    DBcanLimitData shiftedLaplaceFiniteOperatorLayerSigma1.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerExhaustion
    shiftedLaplaceFiniteOperatorLayerSigma1
    (shiftedLaplaceModelPackageAt 1)
    shiftedLaplaceModelExhaustionSigma1

/-- Its `Bcan` agrees with the model on the overlap half-plane. -/
theorem shiftedLaplaceDBcanLimitSigma1_matches_model
    (s : ℂ) (hs : s ∈ RightHalfPlane shiftedLaplaceFiniteOperatorLayerSigma1.toStagePackage.sigma0) :
    shiftedLaplaceDBcanLimitSigma1.Bcan s = shiftedLaplaceLogDerivModel s := by
  have h := canonicalPrimePowerExhaustion_h_Bcan_matches_shared
    shiftedLaplaceFiniteOperatorLayerSigma1
    (shiftedLaplaceModelPackageAt 1)
    shiftedLaplaceModelExhaustionSigma1
    s hs
  -- C.Bshared = shiftedLaplaceLogDerivModel
  simpa [shiftedLaplaceDBcanLimitSigma1, shiftedLaplaceModelPackageAt] using h

#print axioms shiftedLaplaceDBcanLimitSigma1
#print axioms shiftedLaplaceDBcanLimitSigma1_matches_model

end
end RHFormalization
