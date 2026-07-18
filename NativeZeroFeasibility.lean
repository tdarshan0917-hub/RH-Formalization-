import RHFormalization.DNativeUnboundedOperator

namespace RHFormalization

noncomputable section

#check NativeUnboundedDStage
#check NativeUnboundedDStage.mk

#check IsSelfAdjoint
#check LinearPMapLowerSemibounded
#check LinearPMapNonnegative

#check (0 : ℂ →ₗ.[ℂ] ℂ)

example : NativeUnboundedDStage ℂ := by
  refine
    { H := (0 : ℂ →ₗ.[ℂ] ℂ)
      h_selfAdjoint := ?h_selfAdjoint
      h_lowerSemibounded := ?h_lowerSemibounded
      h_shiftedNonnegative := ?h_shiftedNonnegative }

end

end RHFormalization
