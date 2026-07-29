import RHFormalization.ArithmeticShiftedPrimeDExportShiftedLaplace
import RHFormalization.CurrentFrontierSelectedD

namespace RHFormalization
noncomputable section
open Complex

#check ArithmeticShiftedPrimeDExport_of_spectral_gap_shiftedLaplaceBStage
#check ArithmeticShiftedPrimeDExport_of_generic_F_B_bounds
#check selectedFiniteOperatorLayer
#check selectedFiniteOperatorLayer.toStagePackage
#check selectedFiniteOperatorLayer.toStagePackage.F_stage
#check selectedFiniteOperatorLayer.toStagePackage.B_stage
#check selectedFiniteOperatorLayer.toStagePackage.R_stage

/-- Target shape needed by `CurrentFrontierSelectedD`. -/
def selected_h_R_stage_bound_target : Prop :=
  ∀ (K : Set ℂ),
    IsCompact K →
      K ⊆ Ω →
        ∃ C, 0 ≤ C ∧
          ∀ (α : DFiniteStage), ∀ s ∈ K,
            ‖selectedFiniteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C

#check selected_h_R_stage_bound_target

end
end RHFormalization
