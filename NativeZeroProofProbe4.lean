import RHFormalization.DNativeUnboundedOperator

namespace RHFormalization

noncomputable section

example : IsSelfAdjoint (0 : ℂ →ₗ.[ℂ] ℂ) := by
  rw [IsSelfAdjoint]
  ext x
  simp

example : LinearPMapLowerSemibounded (0 : ℂ →ₗ.[ℂ] ℂ) := by
  rw [LinearPMapLowerSemibounded]
  refine ⟨0, ?_⟩
  intro a
  simp

example : LinearPMapNonnegative (0 : ℂ →ₗ.[ℂ] ℂ) := by
  rw [LinearPMapNonnegative]
  intro a
  simp

def zeroNativeUnboundedDStageComplex : NativeUnboundedDStage ℂ :=
  { H := (0 : ℂ →ₗ.[ℂ] ℂ)
    h_selfAdjoint := by
      rw [IsSelfAdjoint]
      ext x
      simp
    h_lowerSemibounded := by
      rw [LinearPMapLowerSemibounded]
      refine ⟨0, ?_⟩
      intro a
      simp
    h_shiftedNonnegative := by
      rw [LinearPMapNonnegative]
      intro a
      simp }

#check zeroNativeUnboundedDStageComplex
#print axioms zeroNativeUnboundedDStageComplex

end

end RHFormalization
