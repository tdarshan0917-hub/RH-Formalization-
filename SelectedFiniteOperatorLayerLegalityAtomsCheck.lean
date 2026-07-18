import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDSpikeSumExtraction

namespace RHFormalization

#check NativeUnboundedDStage
#print NativeUnboundedDStage

#check IsSelfAdjoint
#check LinearPMapLowerSemibounded
#check LinearPMapNonnegative

#check DStageSelfAdjointC
#print DStageSelfAdjointC

#check DStageLowerSemiboundedC
#print DStageLowerSemiboundedC

#check DStageShiftedNonnegativeC
#print DStageShiftedNonnegativeC

#check DFiniteStageOperatorLegality.mk
#check DStageHeatTraceClassC_of_pos
#check DStageResolventTraceLegalC_of_mem_Omega
#check DStageDuhamelTraceNormLegalC_from_majorant
#check DStageDiagonalSpikeExtractionC_from_stage_certificate
#check DStageMixedWordControlC_from_stage_certificate

-- Probe: can the first three legality fields be solved from α.native?
example (α : DFiniteStage) : DStageSelfAdjointC α := by
  unfold DStageSelfAdjointC
  -- leave output if this does not close
  sorry

example (α : DFiniteStage) : DStageLowerSemiboundedC α := by
  unfold DStageLowerSemiboundedC
  sorry

example (α : DFiniteStage) : DStageShiftedNonnegativeC α := by
  unfold DStageShiftedNonnegativeC
  sorry

end RHFormalization
