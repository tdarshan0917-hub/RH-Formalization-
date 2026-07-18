import RHFormalization.DNativeUnboundedOperator

namespace RHFormalization
noncomputable section
open LinearPMap

noncomputable def zeroFull : ℂ →ₗ.[ℂ] ℂ :=
  (0 : ℂ →L[ℂ] ℂ).toPMap ⊤

-- Variant A: erw to see through the coercion, then adjoint_zero
theorem zeroFull_selfAdjoint_A : IsSelfAdjoint zeroFull := by
  rw [LinearPMap.isSelfAdjoint_def]
  show ((0 : ℂ →L[ℂ] ℂ).toPMap ⊤).adjoint = zeroFull
  erw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense
    (by simp [Submodule.top_coe, dense_univ])]
  simp [zeroFull, ContinuousLinearMap.adjoint_zero]

-- Variant B: avoid the lemma entirely; rewrite zeroFull's CLM as adjoint of itself
theorem zeroFull_selfAdjoint_B : IsSelfAdjoint zeroFull := by
  rw [LinearPMap.isSelfAdjoint_def]
  have h0 : (0 : ℂ →L[ℂ] ℂ) = ContinuousLinearMap.adjoint (0 : ℂ →L[ℂ] ℂ) := by
    simp
  show ((0 : ℂ →L[ℂ] ℂ).toPMap ⊤).adjoint = zeroFull
  rw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense
    (by simp [Submodule.top_coe, dense_univ])]
  rw [zeroFull, ← h0]

theorem zeroFull_lowerSemibounded : LinearPMapLowerSemibounded zeroFull := by
  refine ⟨0, ?_⟩
  intro x
  simp [zeroFull, LinearMap.toPMap_apply]

theorem zeroFull_nonneg : LinearPMapNonnegative zeroFull := by
  intro x
  simp [zeroFull, LinearMap.toPMap_apply]

noncomputable def zeroNativeStage : NativeUnboundedDStage ℂ :=
  { H := zeroFull
    h_selfAdjoint := zeroFull_selfAdjoint_A
    h_lowerSemibounded := zeroFull_lowerSemibounded
    h_shiftedNonnegative := zeroFull_nonneg }

#print axioms zeroNativeStage

end
end RHFormalization
