/-
GalerkinStagePackage.lean

The genuine-operator DFiniteStagePackage: F_stage from the stage's own
resolvent trace, B_stage the finite canonical shifted-Laplace prime-power
package at the stage cutoff (the exact form with banked sigma=1 convergence),
R_stage := F_stage - B_stage. The finite split is definitional. sigma0 = 1.
-/
import RHFormalization.GalerkinStageSequence
import RHFormalization.CanonicalPrimePowerPackage
import RHFormalization.ShiftedLaplaceDSharedBridge
import RHFormalization.SupVBound

namespace RHFormalization
noncomputable section

/-- The genuine-operator stage package. -/
def galerkinStagePackage : DFiniteStagePackage :=
  { F_stage := fun α s => α.appendixDFiniteFStage (s + (SupVConst : ℂ))
    B_stage := fun α s =>
      finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow α.R)
        shiftedLaplaceHeatKernelC s
    R_stage := fun α s =>
      α.appendixDFiniteFStage (s + (SupVConst : ℂ)) -
        finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow α.R)
          shiftedLaplaceHeatKernelC s
    sigma0 := 1 }

/-- The finite split holds definitionally: F = B + R. -/
def galerkinStageSplitAPI : DFiniteStageSplitAPI galerkinStagePackage where
  h_stage_split := by
    intro α s _
    show α.appendixDFiniteFStage (s + (SupVConst : ℂ)) =
      finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow α.R)
        shiftedLaplaceHeatKernelC s +
      (α.appendixDFiniteFStage (s + (SupVConst : ℂ)) -
        finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow α.R)
          shiftedLaplaceHeatKernelC s)
    ring

/-- Along the genuine exhaustion, B_stage is the concrete finite canonical
package at cutoff (n:ℝ)+1 — the exact banked-convergence form. -/
theorem galerkinStagePackage_B_at_seq (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (galerkinStageSeq n) s =
      finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow ((n : ℝ) + 1))
        shiftedLaplaceHeatKernelC s := by
  rfl

#print axioms galerkinStagePackage
#print axioms galerkinStageSplitAPI
#print axioms galerkinStagePackage_B_at_seq

end
end RHFormalization
