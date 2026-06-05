import RHFormalization.DOperatorExport
import RHFormalization.DResolventTraceSummability
import RHFormalization.DSuperSmoothing
import RHFormalization.DHeatTraceSummability
import RHFormalization.AppendixDSpikeSumExtraction

/-!
# RHFormalization.DFiniteStageOperator

Iteration 9: finite-stage operator legality layer.

Appendix D starts from fixed finite cutoff/window objects. At this level the
operator-theoretic tasks are finite-stage tasks:

* self-adjointness / lower semiboundedness / global shifted nonnegativity;
* trace-class legality of localized heat and resolvent traces;
* Duhamel/Dyson expansion legality after localization;
* diagonal spike extraction at fixed `(L,R)`;
* construction of the finite-stage functions `F_stage`, `B_stage`, `R_stage`;
* finite-stage split `F_stage = B_stage + R_stage` on the overlap half-plane.

The later Appendix-D export layer then removes cutoffs and proves the canonical
whole-line objects on `Ω`.

This file does not prove the full operator theory in Mathlib. It converts the
finite-stage operator assumptions into precise APIs feeding `DOperatorExport.lean`.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Abstract finite-stage operator predicates

These are intentionally explicit: they mark exactly what must eventually be
discharged by the operator-ideal / trace-class formalization.
-/

/-- Fixed finite-stage self-adjointness, now backed by Mathlib's native `IsSelfAdjoint`. -/
def DStageSelfAdjointC (α : DFiniteStage) : Prop :=
  letI : NormedAddCommGroup α.E := α.instNormed
  letI : InnerProductSpace ℂ α.E := α.instInner
  letI : CompleteSpace α.E := α.instComplete
  IsSelfAdjoint α.native.H

/-- Fixed finite-stage lower semiboundedness before global shift, as a native quadratic-form condition. -/
def DStageLowerSemiboundedC (α : DFiniteStage) : Prop :=
  letI : NormedAddCommGroup α.E := α.instNormed
  letI : InnerProductSpace ℂ α.E := α.instInner
  letI : CompleteSpace α.E := α.instComplete
  LinearPMapLowerSemibounded α.native.H

/-- The globally shifted finite-stage operator is nonnegative, as a native quadratic-form condition. -/
def DStageShiftedNonnegativeC (α : DFiniteStage) : Prop :=
  letI : NormedAddCommGroup α.E := α.instNormed
  letI : InnerProductSpace ℂ α.E := α.instInner
  letI : CompleteSpace α.E := α.instComplete
  LinearPMapNonnegative α.native.H

/-- Localized heat trace legality at fixed finite stage, represented by heat-series summability. -/
def DStageHeatTraceClassC (α : DFiniteStage) (t : ℝ) : Prop :=
  Summable (fun n : ℕ => Real.exp (-t * α.heatEigenvalue n))

/--
The finite-stage heat-trace condition follows from the stored eigenvalue-growth
certificate and the theorem-backed heat summability lemma.
-/
theorem DStageHeatTraceClassC_of_pos
    (α : DFiniteStage)
    {t : ℝ}
    (ht : 0 < t) :
    DStageHeatTraceClassC α t := by
  exact
    summable_heat_exp_of_linear_lower
      (lam := α.heatEigenvalue)
      (a := α.heatScale)
      (t := t)
      α.h_heatScale_pos
      ht
      α.h_heatEigenvalue_linear_lower

/-- Localized resolvent trace legality at fixed finite stage, represented by summability of the spectral resolvent proxy. -/
def DStageResolventTraceLegalC (α : DFiniteStage) (s : ℂ) : Prop :=
  Summable (α.resolventTraceTerm s)

/--
The finite-stage resolvent trace condition follows from the stored p-series comparison bound.
-/
theorem DStageResolventTraceLegalC_of_mem_Omega
    (α : DFiniteStage)
    {s : ℂ}
    (hs : s ∈ Ω) :
    DStageResolventTraceLegalC α s := by
  exact
    summable_complex_of_norm_le_const_one_div_nat_sq
      (f := α.resolventTraceTerm s)
      (C := α.resolventBoundConstant s)
      (α.h_resolventBoundConstant_nonneg s hs)
      (α.h_resolventTraceBound s hs)

/-- Fixed-stage Duhamel/Dyson trace-norm legality, represented by summability of the stage trace-norm term sequence. -/
def DStageDuhamelTraceNormLegalC (α : DFiniteStage) : Prop :=
  Summable α.duhamelTraceNormTerm

/--
The Duhamel trace-norm legality follows from the stored summable majorant certificate.
-/
theorem DStageDuhamelTraceNormLegalC_from_majorant
    (α : DFiniteStage) :
    DStageDuhamelTraceNormLegalC α := by
  exact
    Summable.of_nonneg_of_le
      α.h_duhamelTraceNormTerm_nonneg
      α.h_duhamelTraceNormTerm_bound
      α.h_duhamelMajorant_summable

/-- Fixed-stage diagonal spike extraction, represented by the explicit finite-stage extraction certificate. -/
def DStageDiagonalSpikeExtractionC (α : DFiniteStage) : Prop :=
  ∀ q : ℕ,
    α.diagonalSpikeActive q →
      α.diagonalSpikeContribution q = α.canonicalSpikeContribution q

/--
The diagonal spike extraction condition follows from the stored finite-stage certificate.
-/
theorem DStageDiagonalSpikeExtractionC_from_stage_certificate
    (α : DFiniteStage) :
    DStageDiagonalSpikeExtractionC α :=
  α.h_diagonalSpikeExtraction

/-- Fixed-stage mixed-word/super-smoothing control, represented by super-polynomial decay. -/
def DStageMixedWordControlC (α : DFiniteStage) : Prop :=
  SuperPolynomialDecay α.mixedWordRemainder

/--
The mixed-word control condition follows from the stored finite-stage super-smoothing certificate.
-/
theorem DStageMixedWordControlC_from_stage_certificate
    (α : DFiniteStage) :
    DStageMixedWordControlC α :=
  α.h_mixedWordSuperPolynomialDecay

/-!
## 2. Finite-stage operator legality package
-/

/--
Finite-stage operator legality.

This mirrors Appendices A/B and the fixed-cutoff part of Appendix D.  It is
not yet the whole-line export.
-/
structure DFiniteStageOperatorLegality
    (α : DFiniteStage) where
  h_selfAdjoint :
    DStageSelfAdjointC α
  h_lowerSemibounded :
    DStageLowerSemiboundedC α
  h_shiftedNonnegative :
    DStageShiftedNonnegativeC α
  h_heatTraceClass :
    ∀ t : ℝ, 0 < t → DStageHeatTraceClassC α t
  h_resolventTraceLegal :
    ∀ s : ℂ, s ∈ Ω → DStageResolventTraceLegalC α s
  h_duhamelLegal :
    DStageDuhamelTraceNormLegalC α
  h_diagonalSpikeExtraction :
    DStageDiagonalSpikeExtractionC α
  h_mixedWordControl :
    DStageMixedWordControlC α

/--
Uniform global spectral shift over all finite stages.

This records the manuscript's insistence that a single global shift is used, not
an `L`- or `R`-dependent shift.
-/
structure DGlobalShiftAPI where
  M : ℝ
  h_M_nonnegative :
    0 ≤ M
  h_uniform_shift :
    ∀ α : DFiniteStage, DStageShiftedNonnegativeC α

/-!
## 3. Trace/Duhamel package construction
-/

/--
Finite-stage trace functions produced from the operator legality layer.

This is a Lean-facing wrapper around the finite-stage heat/resolvent trace
construction before the ordered cutoff-removal passage.
-/
structure DFiniteTraceFunctionData where
  F_stage : DFiniteStage → ℂ → ℂ
  B_stage : DFiniteStage → ℂ → ℂ
  R_stage : DFiniteStage → ℂ → ℂ
  sigma0 : ℝ

/--
Finite-stage trace construction API.

Given finite-stage operator legality, construct the finite transform, package,
and remainder functions.
-/
structure DFiniteTraceConstructionAPI where
  h_construct :
    (∀ α : DFiniteStage, DFiniteStageOperatorLegality α) →
    DFiniteTraceFunctionData

/-- Convert finite trace data into the `DFiniteStagePackage` used by D.EXPORT. -/
def DFiniteTraceFunctionData.toStagePackage
    (T : DFiniteTraceFunctionData) :
    DFiniteStagePackage :=
  { F_stage := T.F_stage
    B_stage := T.B_stage
    R_stage := T.R_stage
    sigma0 := T.sigma0 }

/--
Fixed-stage split builder from Duhamel/trace decomposition.

This is the formal bridge from the operator word expansion to
`F_stage = B_stage + R_stage`.
-/
structure DFiniteStageSplitFromDuhamelAPI
    (T : DFiniteTraceFunctionData) where
  h_split :
    DFiniteStageSplitAPI T.toStagePackage

/--
Operator-to-D-stage package layer.

This is the result of formalizing finite-stage operator legality:
it supplies the finite-stage package and the fixed-stage split.
-/
structure DFiniteStagePackageFromOperatorLayer where
  legality :
    ∀ α : DFiniteStage, DFiniteStageOperatorLegality α
  traceConstruction : DFiniteTraceConstructionAPI
  traceData : DFiniteTraceFunctionData
  h_traceData_from_legality :
    traceData = traceConstruction.h_construct legality
  splitFromDuhamel :
    DFiniteStageSplitFromDuhamelAPI traceData

  /--
  Finite spike-sum evidence connecting the operator-layer `B_stage` to the
  canonical prime-power finite package.

  This is the D-side bridge:
  coefficient diagonal extraction
    ⇒ finite spike sum
    ⇒ finite canonical prime-power formula.
  -/
  finiteCanonicalPrimePowerFormula :
    DFiniteStageCanonicalPrimePowerFormula traceData.toStagePackage

/-- Extract the finite-stage package from operator legality. -/
def DFiniteStagePackageFromOperatorLayer.toStagePackage
    (X : DFiniteStagePackageFromOperatorLayer) :
    DFiniteStagePackage :=
  X.traceData.toStagePackage

/-- Extract the fixed-stage split from operator legality. -/
def DFiniteStagePackageFromOperatorLayer.toStageSplit
    (X : DFiniteStagePackageFromOperatorLayer) :
    DFiniteStageSplitAPI X.toStagePackage :=
  X.splitFromDuhamel.h_split

def DFiniteStagePackageFromOperatorLayer.toFiniteCanonicalPrimePowerFormula
    (X : DFiniteStagePackageFromOperatorLayer) :
    DFiniteStageCanonicalPrimePowerFormula X.toStagePackage :=
  X.finiteCanonicalPrimePowerFormula


/-!
## 4. Compatibility with the detailed Appendix-D export layer
-/

/--
Appendix-D detailed construction with finite-stage operator legality included.

Compared with `DDetailedConstructionLayer`, this version does not take the
finite-stage package as a raw field.  It obtains it from the fixed-stage operator
legality layer.
-/
structure DDetailedConstructionWithOperatorLegality where
  finiteOperatorLayer :
    DFiniteStagePackageFromOperatorLayer

  W : DCanonicalWindowData
  Wapi : DCanonicalWindowAPI W

  B : DBcanLimitData finiteOperatorLayer.toStagePackage
  F : DFHLimitData finiteOperatorLayer.toStagePackage

  sectors : DResidualSectorData finiteOperatorLayer.toStagePackage
  sectorSplit :
    DResidualSectorSplitAPI finiteOperatorLayer.toStagePackage sectors
  sectorBounds :
    DResidualSectorBoundsAPI finiteOperatorLayer.toStagePackage sectors

  master :
    DMasterResidualAPI finiteOperatorLayer.toStagePackage sectors

  overlapBuilder :
    let Rdata := master.h_master sectorSplit sectorBounds
    DOverlapIdentityAPI finiteOperatorLayer.toStagePackage B F Rdata

/-- Convert the finite-operator-legality construction into the prior detailed layer. -/
def DDetailedConstructionWithOperatorLegality.toDetailedConstructionLayer
    (X : DDetailedConstructionWithOperatorLegality) :
    DDetailedConstructionLayer :=
  { W := X.W
    Wapi := X.Wapi
    P := X.finiteOperatorLayer.toStagePackage
    finiteSplit := X.finiteOperatorLayer.toStageSplit
    B := X.B
    F := X.F
    sectors := X.sectors
    sectorSplit := X.sectorSplit
    sectorBounds := X.sectorBounds
    master := X.master
    overlapBuilder := X.overlapBuilder }

/-- Extract the D export layer. -/
def DDetailedConstructionWithOperatorLegality.toDExportLayer
    (X : DDetailedConstructionWithOperatorLegality) :
    DExportLayer :=
  X.toDetailedConstructionLayer.toDExportLayer

/-- Extract the operator resolvent bridge consumed by E/F. -/
def DDetailedConstructionWithOperatorLegality.toOperatorResolventBridge
    (X : DDetailedConstructionWithOperatorLegality) :
    OperatorResolventBridge :=
  X.toDetailedConstructionLayer.toOperatorResolventBridge

end

end RHFormalization
