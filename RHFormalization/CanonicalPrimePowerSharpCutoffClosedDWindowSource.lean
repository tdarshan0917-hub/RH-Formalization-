import RHFormalization.SelectedFiniteOperatorLayer
import RHFormalization.CanonicalPrimePowerCountingSetEnvelope
import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedDataClosedSummability
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import RHFormalization.CanonicalPrimePowerExactMassEnvelope

/-!
# Sharp-cutoff closed D-window source

This is the coherent source object for `selectedClosedPayload`.

Important implementation point:

We do not cast `S.kernelID` across window/kernel equalities.  Casting produced
a dependent projection problem at `.coord`.

Instead, we rebuild the sharp `kernelID` with the same coordinate function and
rewrite only the two proof fields.
-/

namespace RHFormalization

noncomputable section

structure SelectedSharpCutoffClosedDWindowSource where
  S :
    CanonicalPrimePowerDWindowMassCountingSetWeightEnvelopeData
      selectedFiniteOperatorLayer

  hW :
    S.W =
      sharpCutoffDCanonicalWindowData
        (heatKernelG (1 : ℝ))
        (fun α : DFiniteStage => α.L)

  hKshared :
    S.Kshared =
      displacementCanonicalKernel (heatKernelG (1 : ℝ))

  sharpSpeed :
    DCanonicalWindowSharpCutoffConcreteChosenSpeedData
      (heatKernelG (1 : ℝ))
      (fun α : DFiniteStage => α.L)
      S.alpha

  hL_chosen :
    ∀ n : ℕ,
      (S.alpha n).L =
        ((exactPrimePowerMassEnvelopeData S.massEnum).massEnvelope
          ((S.alpha n).R) + 1) *
        ((n : ℝ) + 1)

namespace SelectedSharpCutoffClosedDWindowSource

/--
Sharp-cutoff kernel identification rebuilt from `S.kernelID`.

The coordinate function is definitionally the same as `S.kernelID.coord`; only
the window/kernel proof fields are rewritten.
-/
noncomputable def sharpKernelID
    (Src : SelectedSharpCutoffClosedDWindowSource) :
    PrimePowerDWindowKernelIdentificationData
      selectedFiniteOperatorLayer
      (sharpCutoffDCanonicalWindowData
        (heatKernelG (1 : ℝ))
        (fun α : DFiniteStage => α.L))
      Src.S.alpha
      (displacementCanonicalKernel (heatKernelG (1 : ℝ))) :=
{
  coord := Src.S.kernelID.coord

  h_stage_kernel_eq_window := by
    intro s hs n q hq
    have h :=
      Src.S.kernelID.h_stage_kernel_eq_window s hs n q hq
    simpa [Src.hW] using h

  h_shared_kernel_eq_limit := by
    intro s hs q
    have h :=
      Src.S.kernelID.h_shared_kernel_eq_limit s hs q
    simpa [Src.hW, Src.hKshared] using h
}

/--
Coordinate membership follows from `S.h_coord_mem`, because the rebuilt sharp
kernel ID uses the same coordinate function.
-/
theorem h_coord_mem
    (Src : SelectedSharpCutoffClosedDWindowSource) :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
        (Src.S.alpha n) →
        (Src.sharpKernelID).coord s q ∈ Src.S.coordSet s := by
  intro s hs n q hq
  simpa [sharpKernelID] using Src.S.h_coord_mem s hs n q hq

end SelectedSharpCutoffClosedDWindowSource

/--
Build the selected closed heat-kernel payload from the coherent sharp-cutoff
D-window source.
-/
noncomputable def buildSelectedClosedPayloadFromSharpCutoffSource
    (Src : SelectedSharpCutoffClosedDWindowSource) :
    CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload :=
{
  X := selectedFiniteOperatorLayer
  t := (1 : ℝ)
  ht_pos := by norm_num

  Lstage := fun α : DFiniteStage => α.L
  alpha := Src.S.alpha
  sharpSpeed := Src.sharpSpeed

  h_R_ge_nat := Src.S.h_R_ge_nat
  h_indices_contains_of_center_le_R :=
    Src.S.h_indices_contains_of_center_le_R
  h_indices_subset_center_le_R :=
    Src.S.h_indices_subset_center_le_R

  kernelID := Src.sharpKernelID

  coordSet := Src.S.coordSet
  h_coordSet_compact := Src.S.h_coordSet_compact
  h_coord_mem := Src.h_coord_mem

  massEnum := Src.S.massEnum
  massEnvelopeData := exactPrimePowerMassEnvelopeData Src.S.massEnum
  hL_chosen := Src.hL_chosen
}

end

end RHFormalization
