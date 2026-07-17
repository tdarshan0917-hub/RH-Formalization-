import RHFormalization.SelectedFiniteTraceSpikePayload
import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import RHFormalization.CanonicalPrimePowerSharpCutoffHeatKernelWeightedClosedPayload
import RHFormalization.CanonicalPrimePowerDWindowKernelIdentification

/-!
# Appendix-D finite spike extraction witness

This is the actual missing finite Appendix-D source.

It is deliberately not a wrapper around `SelectedY`, closed payloads, or mass
enumeration.  It records the finite diagonal-spike extraction data that
`DFiniteStage` itself does not store:

* finite-stage transform `F_stage`;
* finite active Nat spike set;
* active-set soundness and completeness;
* Nat-to-prime-power map;
* injectivity on active indices;
* coefficient compatibility with canonical prime-power weights.

From this witness, the selected finite trace/spike payload is pure wiring.
-/

namespace RHFormalization

noncomputable section

/--
The real finite Appendix-D extraction witness.

This is the source theorem/object we must eventually prove from the analytic
finite-stage Duhamel/diagonal-spike extraction argument.
-/
structure AppendixDFiniteSpikeExtractionWitness where
  /-- Selected finite-stage operator-side transform. -/
  F_stage : DFiniteStage → ℂ → ℂ

  /-- Finite active diagonal-spike Nat indices at each stage. -/
  activeIndices : DFiniteStage → Finset ℕ

  /-- Soundness: every selected active index is actually stage-active. -/
  h_activeIndices_active :
    ∀ (α : DFiniteStage), ∀ q ∈ activeIndices α,
      α.diagonalSpikeActive q

  /--
  Completeness: every stage-active diagonal spike is selected.

  This is the field that prevents the bogus empty-index payload.
  -/
  h_activeIndices_complete :
    ∀ (α : DFiniteStage), ∀ q : ℕ,
      α.diagonalSpikeActive q →
        q ∈ activeIndices α

  /-- Nat-to-prime-power identification for active spikes. -/
  toPP : DFiniteStage → ℕ → PrimePowerPair

  /-- Injectivity of the Nat-to-prime-power identification on active indices. -/
  hinj :
    ∀ (α : DFiniteStage),
      ∀ m ∈ activeIndices α,
      ∀ n ∈ activeIndices α,
        toPP α m = toPP α n → m = n

  /-- Canonical coefficient compatibility on active indices. -/
  hcoeff :
    ∀ (α : DFiniteStage),
      ∀ n ∈ activeIndices α,
        α.canonicalSpikeContribution n =
          PrimePowerPair.weightC (toPP α n)

/-- Chosen canonical kernel for the finite spike extraction route. -/
noncomputable def AppendixDFiniteSpikeExtractionWitness.Kcan
    (_W : AppendixDFiniteSpikeExtractionWitness) :
    DFiniteStage → CanonicalKernelC :=
  fun _ => displacementCanonicalKernel (heatKernelG (1 : ℝ))

/--
Nat-indexed spike kernel induced by the canonical kernel and the Nat→prime-power
identification.
-/
noncomputable def AppendixDFiniteSpikeExtractionWitness.spikeKernel
    (W : AppendixDFiniteSpikeExtractionWitness) :
    DFiniteStage → ℕ → ℂ → ℂ :=
  fun α n s =>
    W.Kcan α (PrimePowerPair.center (W.toPP α n)) s

/-- Finite diagonal spike part. -/
noncomputable def AppendixDFiniteSpikeExtractionWitness.B_stage
    (W : AppendixDFiniteSpikeExtractionWitness) :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    finiteNatSpikePackage
      (W.activeIndices α)
      α.diagonalSpikeContribution
      (W.spikeKernel α)
      s

/-- Remainder, defined algebraically. -/
noncomputable def AppendixDFiniteSpikeExtractionWitness.R_stage
    (W : AppendixDFiniteSpikeExtractionWitness) :
    DFiniteStage → ℂ → ℂ :=
  fun α s =>
    W.F_stage α s - W.B_stage α s

/-- Fixed selected half-plane threshold for this finite layer. -/
noncomputable def AppendixDFiniteSpikeExtractionWitness.sigma0
    (_W : AppendixDFiniteSpikeExtractionWitness) : ℝ :=
  0

/-- Algebraic split `F = B + R`. -/
theorem AppendixDFiniteSpikeExtractionWitness.h_stage_split
    (W : AppendixDFiniteSpikeExtractionWitness) :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane W.sigma0,
      W.F_stage α s = W.B_stage α s + W.R_stage α s := by
  intro α s hs
  simp [AppendixDFiniteSpikeExtractionWitness.R_stage]

/-- Definitional diagonal-sum identity. -/
theorem AppendixDFiniteSpikeExtractionWitness.h_B_stage_eq_diagonal_sum
    (W : AppendixDFiniteSpikeExtractionWitness) :
    ∀ (α : DFiniteStage) (s : ℂ),
      W.B_stage α s =
        finiteNatSpikePackage
          (W.activeIndices α)
          α.diagonalSpikeContribution
          (W.spikeKernel α)
          s := by
  intro α s
  rfl

/-- Definitional kernel bridge. -/
theorem AppendixDFiniteSpikeExtractionWitness.hkernel
    (W : AppendixDFiniteSpikeExtractionWitness) :
    ∀ (α : DFiniteStage),
      ∀ n ∈ W.activeIndices α,
      ∀ (s : ℂ),
        W.spikeKernel α n s =
          W.Kcan α (PrimePowerPair.center (W.toPP α n)) s := by
  intro α n hn s
  rfl

/--
Build the selected finite trace/spike payload from the real Appendix-D witness.
-/
noncomputable def AppendixDFiniteSpikeExtractionWitness.toSelectedFiniteTraceSpikePayload
    (W : AppendixDFiniteSpikeExtractionWitness) :
    SelectedFiniteTraceSpikePayload :=
  buildSelectedFiniteTraceSpikePayloadFromImageBridge
    W.F_stage
    W.B_stage
    W.R_stage
    W.sigma0
    W.h_stage_split
    W.activeIndices
    W.spikeKernel
    W.h_activeIndices_active
    W.h_B_stage_eq_diagonal_sum
    W.toPP
    W.Kcan
    W.hinj
    W.hcoeff
    W.hkernel

/--
Build the selected finite operator layer from the real Appendix-D witness.
-/
noncomputable def AppendixDFiniteSpikeExtractionWitness.toSelectedFiniteOperatorLayer
    (W : AppendixDFiniteSpikeExtractionWitness) :
    DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromTraceSpikePayload
    W.toSelectedFiniteTraceSpikePayload

end

end RHFormalization
