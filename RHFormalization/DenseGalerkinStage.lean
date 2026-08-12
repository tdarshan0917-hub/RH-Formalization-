/-
DENSE SCHEDULE — Brick D2: the dense Galerkin stage sequence.
Verbatim transcription of `adaptiveGalerkinStageSeq` (AdaptiveGalerkinStage.lean)
with exactly three substitutions: adaptiveL c n → denseL n, adaptiveN c n →
denseN n, adaptiveDensityC c n → denseDensityC n. No `c` parameter. Cutoff
(admR n), codes, ppWeightReal, spike machinery, normalization all UNCHANGED
per frozen invariants. Plus the two rfl-level accessor facts (B_stage form,
stage.L value) that downstream bricks read.
-/

import RHFormalization.DenseGalerkinSchedule
import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.DecodedAnchorDischarge
import RHFormalization.GalerkinStagePackage
import Mathlib

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

/-- Dense density prefactor `1/(2·denseL n)` as a complex constant. -/
def denseDensityC (n : ℕ) : ℂ :=
  ((1 / (2 * denseL n) : ℝ) : ℂ)

/-- **THE DENSE STAGE SEQUENCE.** Identical to `admissibleGalerkinStageSeq`
except window `denseL n` and dimension `denseN n`; cutoff, codes, and spike
fields unchanged. -/
def denseGalerkinStageSeq (n : ℕ) : DFiniteStage :=
  { galerkinOperatorDFiniteStage_ofShift (N := denseN n) n
      (galerkinFreeMu (denseN n) (denseL n))
      1
      (activePrimePowerCodesCenterBelow (admR n))
      ppWeightReal
      (denseL n)
      (galerkinStageShift (denseN n)
        (galerkinFreeMu (denseN n) (denseL n)) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (denseL n))
      (galerkinStageShift_spec (denseN n)
        (galerkinFreeMu (denseN n) (denseL n)) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (denseL n))
    with
    L := denseL n
    hL_pos := denseL_pos n
    R := admR n
    hR_pos := admR_pos n
    diagonalSpikeActive := fun k => k ∈ admStageCodes n
    diagonalSpikeContribution := fun k => (ppDecode k).weightC
    canonicalSpikeContribution := fun k => (ppDecode k).weightC
    h_diagonalSpikeExtraction := by intro k _; rfl
    diagonalSpikeActiveIndices := admStageCodes n
    h_diagonalSpikeActiveIndices_active := by intro k hk; exact hk
    h_diagonalSpikeActiveIndices_complete := by intro k hk; exact hk
    diagonalSpikeToPP := ppDecode
    h_diagonalSpikeToPP_inj := by
      intro a _ b _ h
      have h2 := congrArg ppCode h
      simpa [ppCode_ppDecode] using h2
    h_canonicalSpikeContribution_eq_weightC := by intro k _; rfl
    h_diagonalSpikeToPP_center_le_R := by
      classical
      intro k hk
      rcases mem_admStageCodes.mp hk with ⟨q, hq, rfl⟩
      have hfil := Finset.mem_filter.mp hq
      have hcenter := hfil.2.2
      simpa [ppDecode_ppCode] using hcenter
    h_diagonalSpikeToPP_complete_center_le_R := by
      classical
      intro q hq hle
      have hbelow : q ∈ concretePrimePowerBelowCutoff (admR n) :=
        concretePrimePowerEnum.h_mem_belowCutoff (admR n) q hq hle
      refine ⟨ppCode q, ?_, ppDecode_ppCode q⟩
      exact mem_admStageCodes.mpr ⟨q, hbelow, rfl⟩
    appendixDFiniteFStage := fun s =>
      denseDensityC n *
        galerkinPerturbedFStage (N := denseN n)
          (galerkinFreeMu (denseN n) (denseL n)) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (denseL n) s }

/-- The dense stage carries the dense window. -/
theorem denseGalerkinStageSeq_L (n : ℕ) :
    (denseGalerkinStageSeq n).L = denseL n := rfl

/-- The dense stage carries the admissible cutoff. -/
theorem denseGalerkinStageSeq_R (n : ℕ) :
    (denseGalerkinStageSeq n).R = admR n := rfl

/-- **B_stage schedule-independence**: the dense stage's B-side package
agrees with the admissible one (it depends only on the cutoff `admR n`,
never on `L` or `N`). Mirrors the `hBB` step inside
`RH_from_pairedTransform_locbdd`. -/
theorem denseGalerkinStage_B_stage_eq (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (denseGalerkinStageSeq n) s
      = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
  first
    | rfl
    | (show finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (denseGalerkinStageSeq n).R)
          shiftedLaplaceHeatKernelC s = _
       rfl)

#print axioms denseGalerkinStageSeq
#print axioms denseGalerkinStageSeq_L
#print axioms denseGalerkinStageSeq_R
#print axioms denseGalerkinStage_B_stage_eq

end

end RHFormalization
