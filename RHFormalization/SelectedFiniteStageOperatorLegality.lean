import RHFormalization.DFiniteStageOperator

/-!
# Selected finite-stage operator legality

This file closes the legality component needed by
`selectedFiniteOperatorLayer`.
-/

namespace RHFormalization

noncomputable section

theorem DStageSelfAdjointC_from_native
  (α : DFiniteStage) :
  DStageSelfAdjointC α := by
  letI : NormedAddCommGroup α.E := α.instNormed
  letI : InnerProductSpace ℂ α.E := α.instInner
  letI : CompleteSpace α.E := α.instComplete
  unfold DStageSelfAdjointC
  exact α.native.h_selfAdjoint

theorem DStageLowerSemiboundedC_from_native
  (α : DFiniteStage) :
  DStageLowerSemiboundedC α := by
  letI : NormedAddCommGroup α.E := α.instNormed
  letI : InnerProductSpace ℂ α.E := α.instInner
  letI : CompleteSpace α.E := α.instComplete
  unfold DStageLowerSemiboundedC
  exact α.native.h_lowerSemibounded

theorem DStageShiftedNonnegativeC_from_native
  (α : DFiniteStage) :
  DStageShiftedNonnegativeC α := by
  letI : NormedAddCommGroup α.E := α.instNormed
  letI : InnerProductSpace ℂ α.E := α.instInner
  letI : CompleteSpace α.E := α.instComplete
  unfold DStageShiftedNonnegativeC
  exact α.native.h_shiftedNonnegative

def selectedFiniteStageOperatorLegality :
  ∀ α : DFiniteStage, DFiniteStageOperatorLegality α := by
  intro α
  exact
    DFiniteStageOperatorLegality.mk
      (DStageSelfAdjointC_from_native α)
      (DStageLowerSemiboundedC_from_native α)
      (DStageShiftedNonnegativeC_from_native α)
      (fun t ht => DStageHeatTraceClassC_of_pos α ht)
      (fun s hs => DStageResolventTraceLegalC_of_mem_Omega α hs)
      (DStageDuhamelTraceNormLegalC_from_majorant α)
      (DStageDiagonalSpikeExtractionC_from_stage_certificate α)
      (DStageMixedWordControlC_from_stage_certificate α)

end

end RHFormalization
