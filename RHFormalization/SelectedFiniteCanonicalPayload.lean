import RHFormalization.SelectedFiniteStageOperatorLegality
import RHFormalization.DFiniteStageOperator

/-!
# Selected finite canonical payload

This is the corrected D-side selected finite operator payload boundary.

It bypasses the old Nat-indexed `SelectedFiniteTraceSpikePayload` / `spikeSumData`
layer and asks directly for the canonical finite prime-power formula that the
downstream D pipeline actually consumes:

* finite-stage trace functions `F_stage`, `B_stage`, `R_stage`;
* the finite Duhamel split `F_stage = B_stage + R_stage`;
* canonical prime-power finite indices and kernel;
* the equality `B_stage = finiteCanonicalPrimePowerPackage`.

This file is still conditional. It does not pretend that the actual selected
finite Appendix-D extraction has been built.
-/

namespace RHFormalization

noncomputable section

structure SelectedFiniteCanonicalPayload where
  F_stage : DFiniteStage → ℂ → ℂ
  B_stage : DFiniteStage → ℂ → ℂ
  R_stage : DFiniteStage → ℂ → ℂ
  sigma0 : ℝ

  h_stage_split :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane sigma0,
      F_stage α s = B_stage α s + R_stage α s

  indices : DFiniteStage → Finset PrimePowerPair
  kernel : DFiniteStage → CanonicalKernelC

  h_B_stage_eq_finiteCanonical :
    ∀ (α : DFiniteStage) (s : ℂ),
      B_stage α s =
        finiteCanonicalPrimePowerPackage
          (indices α)
          (kernel α)
          s

def SelectedFiniteCanonicalPayload.toTraceData
    (Pld : SelectedFiniteCanonicalPayload) :
    DFiniteTraceFunctionData :=
  DFiniteTraceFunctionData.mk
    Pld.F_stage
    Pld.B_stage
    Pld.R_stage
    Pld.sigma0

def SelectedFiniteCanonicalPayload.toTraceConstruction
    (Pld : SelectedFiniteCanonicalPayload) :
    DFiniteTraceConstructionAPI :=
  DFiniteTraceConstructionAPI.mk
    (fun _legality => Pld.toTraceData)

theorem SelectedFiniteCanonicalPayload.h_traceData_from_legality
    (Pld : SelectedFiniteCanonicalPayload) :
    Pld.toTraceData =
      Pld.toTraceConstruction.h_construct
        selectedFiniteStageOperatorLegality := by
  rfl

def SelectedFiniteCanonicalPayload.toSplitFromDuhamel
    (Pld : SelectedFiniteCanonicalPayload) :
    DFiniteStageSplitFromDuhamelAPI Pld.toTraceData :=
  DFiniteStageSplitFromDuhamelAPI.mk <|
    DFiniteStageSplitAPI.mk (by
      intro α s hs
      simpa
        [SelectedFiniteCanonicalPayload.toTraceData,
         DFiniteTraceFunctionData.toStagePackage]
        using Pld.h_stage_split α s hs)

def SelectedFiniteCanonicalPayload.toFiniteCanonicalPrimePowerFormula
    (Pld : SelectedFiniteCanonicalPayload) :
    DFiniteStageCanonicalPrimePowerFormula
      Pld.toTraceData.toStagePackage :=
  DFiniteStageCanonicalPrimePowerFormula.mk
    Pld.indices
    Pld.kernel
    (by
      intro α s
      simpa
        [SelectedFiniteCanonicalPayload.toTraceData,
         DFiniteTraceFunctionData.toStagePackage]
        using Pld.h_B_stage_eq_finiteCanonical α s)

def buildSelectedFiniteOperatorLayerFromCanonicalPayload
    (Pld : SelectedFiniteCanonicalPayload) :
    DFiniteStagePackageFromOperatorLayer :=
{
  legality := selectedFiniteStageOperatorLegality
  traceConstruction := Pld.toTraceConstruction
  traceData := Pld.toTraceData
  h_traceData_from_legality := Pld.h_traceData_from_legality
  splitFromDuhamel := Pld.toSplitFromDuhamel
  finiteCanonicalPrimePowerFormula :=
    Pld.toFiniteCanonicalPrimePowerFormula
}

end

end RHFormalization
