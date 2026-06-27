import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.AppendixDFiniteSpikeExtractionWitnessInstance
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerDWindowKernelIdentification
/-!
# Selected finite canonical payload instance

This is the real Appendix-D finite extraction target.

No axiom is introduced here.

The key reduction is definitional:
* `B_stage` is defined to be the finite canonical prime-power package;
* `R_stage` is defined as `F_stage - B_stage`.

Therefore the two structural proof fields,
`h_stage_split` and `h_B_stage_eq_finiteCanonical`,
are no longer separate analytic mysteries.

The remaining real Appendix-D providers are:
* selected finite-stage operator transform `F_stage`;
* selected overlap half-plane parameter `sigma0`;
* selected finite prime-power indices;
* selected canonical kernel.
-/

namespace RHFormalization

noncomputable section

/--
The finite-stage operator-side transform exported by Appendix D.

This is the first real mathematical provider. It must be the actual finite
regularized/operator trace transform, not a dummy function.
-/
noncomputable def selectedFiniteFStage :
    DFiniteStage → ℂ → ℂ :=
  selectedAppendixDFiniteSpikeExtractionWitness.F_stage

/--
The selected half-plane threshold for the finite-stage split.
-/
noncomputable def selectedFiniteSigma0 : ℝ :=
  0

/--
The finite prime-power indices selected at each finite stage.
-/
noncomputable def selectedFiniteIndices :
    DFiniteStage → Finset PrimePowerPair :=
  fun α =>
    (selectedAppendixDFiniteSpikeExtractionWitness.activeIndices α).image
      (fun n => selectedAppendixDFiniteSpikeExtractionWitness.toPP α n)

/--
The selected canonical kernel at each finite stage.
-/
noncomputable def selectedFiniteKernel :
    DFiniteStage → CanonicalKernelC :=
  fun _ => displacementCanonicalKernel (heatKernelG (1 : ℝ))

/--
The finite-stage canonical prime-power part.

This is defined directly as the finite canonical package, so the
`B_stage = finiteCanonicalPrimePowerPackage` proof becomes definitional.
-/
noncomputable def selectedFiniteBStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    finiteCanonicalPrimePowerPackage
      (selectedFiniteIndices α)
      (selectedFiniteKernel α)
      s

/--
The finite-stage remainder.

This definition makes the stage split `F = B + R` algebraic.
-/
noncomputable def selectedFiniteRStage :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    selectedFiniteFStage α s - selectedFiniteBStage α s

/--
The finite-stage trace-function data.
-/
noncomputable def selectedFiniteTraceFunctionData :
    DFiniteTraceFunctionData :=
  DFiniteTraceFunctionData.mk
    selectedFiniteFStage
    selectedFiniteBStage
    selectedFiniteRStage
    selectedFiniteSigma0

/--
The Duhamel split package.

Because `R_stage` is defined as `F_stage - B_stage`, the split is now
an algebraic identity.
-/
noncomputable def selectedFiniteStageSplitFromDuhamel :
    DFiniteStageSplitFromDuhamelAPI selectedFiniteTraceFunctionData :=
by
  refine DFiniteStageSplitFromDuhamelAPI.mk ?_
  refine DFiniteStageSplitAPI.mk ?_
  intro α s hs
  change
    selectedFiniteFStage α s =
      selectedFiniteBStage α s + selectedFiniteRStage α s
  simp [selectedFiniteRStage]

/--
The direct finite canonical prime-power formula.

Because `B_stage` was defined as the finite canonical package, this proof
is definitional.
-/
noncomputable def selectedFiniteCanonicalPrimePowerFormula :
    DFiniteStageCanonicalPrimePowerFormula
      selectedFiniteTraceFunctionData.toStagePackage :=
by
  refine
    DFiniteStageCanonicalPrimePowerFormula.mk
      selectedFiniteIndices
      selectedFiniteKernel
      ?_
  intro α s
  change
    selectedFiniteBStage α s =
      finiteCanonicalPrimePowerPackage
        (selectedFiniteIndices α)
        (selectedFiniteKernel α)
        s
  rfl

/--
The selected finite canonical payload.

This is the object needed upstream by
`buildSelectedFiniteOperatorLayerFromCanonicalPayload`.
-/
noncomputable def selectedFiniteCanonicalPayload :
    SelectedFiniteCanonicalPayload :=
{
  F_stage := selectedFiniteFStage
  B_stage := selectedFiniteBStage
  R_stage := selectedFiniteRStage
  sigma0 := selectedFiniteSigma0
  h_stage_split := by
    intro α s hs
    change
      selectedFiniteFStage α s =
        selectedFiniteBStage α s + selectedFiniteRStage α s
    simp [selectedFiniteRStage]
  indices := selectedFiniteIndices
  kernel := selectedFiniteKernel
  h_B_stage_eq_finiteCanonical := by
    intro α s
    change
      selectedFiniteBStage α s =
        finiteCanonicalPrimePowerPackage
          (selectedFiniteIndices α)
          (selectedFiniteKernel α)
          s
    rfl
}

end

end RHFormalization
