import RHFormalization.DOverlapPointwiseFromCompactUniform
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDetailedConstruction
import RHFormalization.AppendixDPrimePowerLimitReduction
import RHFormalization.HalfPlaneGeometry

namespace RHFormalization

variable (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)

#check SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S
#check (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S).alpha
#check S.alpha

#check
  (buildDOperatorPrimePowerLimitAtOverlapData_fromFiniteCanonicalLimit
    finiteOperatorLayer
    (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
    (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S)).alpha

#check
  (buildDOperatorPrimePowerLimitAtOverlapData_fromFiniteCanonicalLimit
    finiteOperatorLayer
    (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
    (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S)).h_B_stage_tendsto_Bcan

#check
  (buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
    finiteOperatorLayer
    (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
    (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S)).Bcan

#check
  (buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
    finiteOperatorLayer
    (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
    (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S)).h_Bcan_matches_shared

-- These two examples test definitional alpha alignment.
example :
    (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S).alpha = S.alpha := by
  rfl

example :
    (buildDOperatorPrimePowerLimitAtOverlapData_fromFiniteCanonicalLimit
      finiteOperatorLayer
      (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
      (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S)).alpha = S.alpha := by
  rfl

-- This tests whether Bdata.Bcan is definitionally the shared B function.
example (s : ℂ) :
    (buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
      finiteOperatorLayer
      (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
      (SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S)).Bcan s =
    (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S).Bshared s := by
  rfl

#check RightHalfPlane
#check Omega

end RHFormalization
