import RHFormalization.SelectedFiniteTraceSpikePayload
import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerDWindowKernelIdentification

/-!
# Selected finite trace/spike payload instance

This is the correct selected finite Appendix-D extraction target.

It does not use the mass-enum cutoff API.  That was the wrong source for the
selected finite D extraction.

This file reduces all algebraic fields definitionally and leaves only the real
finite Appendix-D extraction data:
* `F_stage`;
* active Nat spike indices;
* proof active indices are active;
* Nat-to-prime-power map;
* injectivity on active indices;
* coefficient compatibility.
-/

namespace RHFormalization

noncomputable section

/-- Selected finite-stage operator transform. -/
noncomputable def selectedTraceFStage :
    DFiniteStage → ℂ → ℂ :=
by
  exact ?F_stage

/-- Selected half-plane threshold. -/
noncomputable def selectedTraceSigma0 : ℝ :=
  0

/-- Selected active diagonal-spike Nat indices. -/
noncomputable def selectedTraceActiveIndices :
    DFiniteStage → Finset ℕ :=
by
  exact ?activeIndices

/-- Selected Nat-to-prime-power bridge. -/
noncomputable def selectedTraceToPP :
    DFiniteStage → ℕ → PrimePowerPair :=
by
  exact ?toPP

/-- Selected canonical kernel. -/
noncomputable def selectedTraceKcan :
    DFiniteStage → CanonicalKernelC :=
  fun _ => displacementCanonicalKernel (heatKernelG (1 : ℝ))

/--
Selected Nat-indexed spike kernel.

This is defined from the canonical kernel and the Nat-to-prime-power map, so
the `hkernel` bridge proof is definitional.
-/
noncomputable def selectedTraceSpikeKernel :
    DFiniteStage → ℕ → ℂ → ℂ :=
  fun α n s =>
    selectedTraceKcan α (PrimePowerPair.center (selectedTraceToPP α n)) s

/--
Selected finite canonical part.

This is exactly the finite Nat spike package using the diagonal contribution.
-/
noncomputable def selectedTraceBStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    finiteNatSpikePackage
      (selectedTraceActiveIndices α)
      α.diagonalSpikeContribution
      (selectedTraceSpikeKernel α)
      s

/--
Selected remainder, defined so that `F = B + R` is algebraic.
-/
noncomputable def selectedTraceRStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    selectedTraceFStage α s - selectedTraceBStage α s

/-- Algebraic stage split. -/
theorem selectedTraceStageSplit :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane selectedTraceSigma0,
      selectedTraceFStage α s =
        selectedTraceBStage α s + selectedTraceRStage α s := by
  intro α s hs
  simp [selectedTraceRStage]

/-- Definitional diagonal-sum identity. -/
theorem selectedTraceBStage_eq_diagonal_sum :
    ∀ (α : DFiniteStage) (s : ℂ),
      selectedTraceBStage α s =
        finiteNatSpikePackage
          (selectedTraceActiveIndices α)
          α.diagonalSpikeContribution
          (selectedTraceSpikeKernel α)
          s := by
  intro α s
  rfl

/-- Definitional kernel bridge. -/
theorem selectedTraceKernelBridge :
    ∀ (α : DFiniteStage), ∀ n ∈ selectedTraceActiveIndices α, ∀ (s : ℂ),
      selectedTraceSpikeKernel α n s =
        selectedTraceKcan α (PrimePowerPair.center (selectedTraceToPP α n)) s := by
  intro α n hn s
  rfl

/--
The selected finite trace/spike payload.

The only remaining holes should be:
* active index activity;
* injectivity of `selectedTraceToPP` on active indices;
* coefficient compatibility.
Plus the definitions of `F_stage`, `activeIndices`, and `toPP` above.
-/
noncomputable def selectedFiniteTraceSpikePayload :
    SelectedFiniteTraceSpikePayload :=
  buildSelectedFiniteTraceSpikePayloadFromImageBridge
    selectedTraceFStage
    selectedTraceBStage
    selectedTraceRStage
    selectedTraceSigma0
    selectedTraceStageSplit
    selectedTraceActiveIndices
    selectedTraceSpikeKernel
    ?h_activeIndices_active
    selectedTraceBStage_eq_diagonal_sum
    selectedTraceToPP
    selectedTraceKcan
    ?hinj
    ?hcoeff
    selectedTraceKernelBridge

end

end RHFormalization
