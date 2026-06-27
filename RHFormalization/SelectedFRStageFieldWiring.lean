import RHFormalization.SelectedFRConcreteTargets
import RHFormalization.AppendixDFiniteSpikeExtractionWitnessInstance
import RHFormalization.ArithmeticPrimeResidualWitnessBridge
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Selected F/R stage-field wiring.

This records that the selected finite operator layer is definitionally the
banked stage-field Appendix-D witness on F_stage and R_stage.
-/

theorem selected_F_stage_eq_stageField
    (α : DFiniteStage) (s : ℂ) :
    selectedFiniteOperatorLayer.toStagePackage.F_stage α s =
      stageFieldSpikeExtractionWitness.F_stage α s := by
  rfl

theorem selected_R_stage_eq_stageField
    (α : DFiniteStage) (s : ℂ) :
    selectedFiniteOperatorLayer.toStagePackage.R_stage α s =
      stageFieldSpikeExtractionWitness.R_stage α s := by
  rfl

#print axioms selected_F_stage_eq_stageField
#print axioms selected_R_stage_eq_stageField

end
end RHFormalization
