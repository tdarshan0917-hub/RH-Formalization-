import RHFormalization.SelectedFiniteStageOperatorLegality
import RHFormalization.AppendixDSpikeSumExtraction

/-!
# Selected finite trace/spike payload

This file isolates the exact remaining non-legality data needed to build
`selectedFiniteOperatorLayer`.

It does not choose dummy trace/spike data.  It packages the real finite-stage
trace split and canonical prime-power spike-sum bridge into one payload.
-/

namespace RHFormalization

noncomputable section

/--
The remaining finite-stage trace/split/spike payload needed after
`selectedFiniteStageOperatorLegality` is closed.
-/
structure SelectedFiniteTraceSpikePayload where
  F_stage : DFiniteStage → ℂ → ℂ
  B_stage : DFiniteStage → ℂ → ℂ
  R_stage : DFiniteStage → ℂ → ℂ
  sigma0 : ℝ

  h_stage_split :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane sigma0,
      F_stage α s = B_stage α s + R_stage α s

  activeIndices : DFiniteStage → Finset ℕ
  spikeKernel : DFiniteStage → ℕ → ℂ → ℂ

  h_activeIndices_active :
    ∀ (α : DFiniteStage), ∀ q ∈ activeIndices α,
      α.diagonalSpikeActive q

  h_B_stage_eq_diagonal_sum :
    ∀ (α : DFiniteStage) (s : ℂ),
      B_stage α s =
        finiteNatSpikePackage
          (activeIndices α)
          α.diagonalSpikeContribution
          (spikeKernel α)
          s

  ppIndices : DFiniteStage → Finset PrimePowerPair
  ppKernel : DFiniteStage → CanonicalKernelC

  h_canonical_sum_eq_finiteCanonical :
    ∀ (α : DFiniteStage) (s : ℂ),
      finiteNatSpikePackage
        (activeIndices α)
        α.canonicalSpikeContribution
        (spikeKernel α)
        s =
      finiteCanonicalPrimePowerPackage
        (ppIndices α)
        (ppKernel α)
        s

/-- The trace data exported by a selected finite trace/spike payload. -/
def SelectedFiniteTraceSpikePayload.toTraceData
  (Pld : SelectedFiniteTraceSpikePayload) :
  DFiniteTraceFunctionData :=
DFiniteTraceFunctionData.mk
  Pld.F_stage
  Pld.B_stage
  Pld.R_stage
  Pld.sigma0

/-- The trace-construction API attached to the payload. -/
def SelectedFiniteTraceSpikePayload.toTraceConstruction
  (Pld : SelectedFiniteTraceSpikePayload) :
  DFiniteTraceConstructionAPI :=
DFiniteTraceConstructionAPI.mk
  (fun _legality => Pld.toTraceData)

/-- The trace data is definitionally what the construction returns. -/
theorem SelectedFiniteTraceSpikePayload.h_traceData_from_legality
  (Pld : SelectedFiniteTraceSpikePayload) :
  Pld.toTraceData =
    Pld.toTraceConstruction.h_construct
      selectedFiniteStageOperatorLegality := by
  rfl

/-- The Duhamel split API attached to the payload. -/
def SelectedFiniteTraceSpikePayload.toSplitFromDuhamel
  (Pld : SelectedFiniteTraceSpikePayload) :
  DFiniteStageSplitFromDuhamelAPI Pld.toTraceData :=
DFiniteStageSplitFromDuhamelAPI.mk <|
  DFiniteStageSplitAPI.mk (by
    intro α s hs
    simpa
      [SelectedFiniteTraceSpikePayload.toTraceData,
       DFiniteTraceFunctionData.toStagePackage]
      using Pld.h_stage_split α s hs)

/-- The finite spike-sum data attached to the payload. -/
def SelectedFiniteTraceSpikePayload.toSpikeSumData
  (Pld : SelectedFiniteTraceSpikePayload) :
  DFiniteStageSpikeSumData Pld.toTraceData.toStagePackage :=
DFiniteStageSpikeSumData.mk
  Pld.activeIndices
  Pld.spikeKernel
  Pld.h_activeIndices_active
  (by
    intro α s
    simpa
      [SelectedFiniteTraceSpikePayload.toTraceData,
       DFiniteTraceFunctionData.toStagePackage]
      using Pld.h_B_stage_eq_diagonal_sum α s)
  Pld.ppIndices
  Pld.ppKernel
  Pld.h_canonical_sum_eq_finiteCanonical

/--
Build the selected finite operator layer from the actual finite trace/spike payload.
-/
def buildSelectedFiniteOperatorLayerFromTraceSpikePayload
  (Pld : SelectedFiniteTraceSpikePayload) :
  DFiniteStagePackageFromOperatorLayer :=
{
  legality := selectedFiniteStageOperatorLegality
  traceConstruction := Pld.toTraceConstruction
  traceData := Pld.toTraceData
  h_traceData_from_legality := Pld.h_traceData_from_legality
  splitFromDuhamel := Pld.toSplitFromDuhamel
  spikeSumData := Pld.toSpikeSumData
}

end

end RHFormalization
