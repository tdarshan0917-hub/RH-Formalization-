import RHFormalization.DNativeUnboundedOperator

namespace RHFormalization
noncomputable section
open LinearPMap

noncomputable def zeroFull : ℂ →ₗ.[ℂ] ℂ :=
  (0 : ℂ →L[ℂ] ℂ).toPMap ⊤

-- explicit-argument application of the Mathlib lemma, no rw pattern-matching
theorem zeroFull_selfAdjoint : IsSelfAdjoint zeroFull := by
  have hdense : Dense ((⊤ : Submodule ℂ ℂ) : Set ℂ) := by
    simp [Submodule.top_coe]
  have key :=
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense
      (A := (0 : ℂ →L[ℂ] ℂ)) hdense
  have hadj0 : ContinuousLinearMap.adjoint (0 : ℂ →L[ℂ] ℂ) = 0 := by
    simp
  rw [LinearPMap.isSelfAdjoint_def]
  calc zeroFull† = (ContinuousLinearMap.adjoint (0 : ℂ →L[ℂ] ℂ)).toPMap ⊤ := key
    _ = ((0 : ℂ →L[ℂ] ℂ)).toPMap ⊤ := by rw [hadj0]
    _ = zeroFull := rfl

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
