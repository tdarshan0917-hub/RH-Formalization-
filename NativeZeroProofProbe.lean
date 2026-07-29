import RHFormalization.DNativeUnboundedOperator

namespace RHFormalization

noncomputable section

#print IsSelfAdjoint
#print LinearPMapLowerSemibounded
#print LinearPMapNonnegative

example : IsSelfAdjoint (0 : ℂ →ₗ.[ℂ] ℂ) := by
  simp [IsSelfAdjoint]

example : LinearPMapLowerSemibounded (0 : ℂ →ₗ.[ℂ] ℂ) := by
  simp [LinearPMapLowerSemibounded]

example : LinearPMapNonnegative (0 : ℂ →ₗ.[ℂ] ℂ) := by
  simp [LinearPMapNonnegative]

example : NativeUnboundedDStage ℂ := by
  refine
    { H := (0 : ℂ →ₗ.[ℂ] ℂ)
      h_selfAdjoint := ?_
      h_lowerSemibounded := ?_
      h_shiftedNonnegative := ?_ }
  · simp [IsSelfAdjoint]
  · simp [LinearPMapLowerSemibounded]
  · simp [LinearPMapNonnegative]

end

end RHFormalization
