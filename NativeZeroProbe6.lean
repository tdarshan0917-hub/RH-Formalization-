import RHFormalization.DNativeUnboundedOperator

namespace RHFormalization
noncomputable section
open LinearPMap

noncomputable def zeroFull : ℂ →ₗ.[ℂ] ℂ :=
  (0 : ℂ →L[ℂ] ℂ).toPMap ⊤

theorem zeroFull_selfAdjoint : IsSelfAdjoint zeroFull := by
  rw [LinearPMap.isSelfAdjoint_def]
  show ((0 : ℂ →L[ℂ] ℂ).toPMap ⊤).adjoint = zeroFull
  rw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense
    (by simpa using dense_univ)]
  simp [zeroFull]

theorem zeroFull_lowerSemibounded : LinearPMapLowerSemibounded zeroFull := by
  refine ⟨0, ?_⟩
  intro x
  simp [zeroFull, LinearMap.toPMap_apply]

theorem zeroFull_nonneg : LinearPMapNonnegative zeroFull := by
  intro x
  simp [zeroFull, LinearMap.toPMap_apply]

noncomputable def zeroNativeStage : NativeUnboundedDStage ℂ :=
  { H := zeroFull
    h_selfAdjoint := zeroFull_selfAdjoint
    h_lowerSemibounded := zeroFull_lowerSemibounded
    h_shiftedNonnegative := zeroFull_nonneg }

#print axioms zeroNativeStage

end
end RHFormalization
