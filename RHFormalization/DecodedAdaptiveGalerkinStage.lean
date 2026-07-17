-- SENTINEL: decoded-adaptive-galerkin-stage-v1
import RHFormalization.AdaptiveGalerkinStage
import RHFormalization.DecodedGalerkinOpNonnegDischarge
import RHFormalization.DecodedGalerkinPerturbedFStage
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- The adaptive Galerkin stage using the manuscript-faithful decoded-center
operator in both its native operator and its perturbed F-stage. -/
def decodedAdaptiveGalerkinStageSeq
    (c : ℝ) (n : ℕ) : DFiniteStage :=
  { decodedGalerkinOperatorDFiniteStage_ofShift
      (N := adaptiveN c n)
      n
      (galerkinFreeMu
        (adaptiveN c n)
        (adaptiveL c n))
      1
      (activePrimePowerCodesCenterBelow (admR n))
      ppWeightReal
      (adaptiveL c n)
      (decodedGalerkinStageShift
        (adaptiveN c n)
        (galerkinFreeMu
          (adaptiveN c n)
          (adaptiveL c n))
        1
        (activePrimePowerCodesCenterBelow (admR n))
        ppWeightReal
        (adaptiveL c n))
      (decodedGalerkinStageShift_spec
        (adaptiveN c n)
        (galerkinFreeMu
          (adaptiveN c n)
          (adaptiveL c n))
        1
        (activePrimePowerCodesCenterBelow (admR n))
        ppWeightReal
        (adaptiveL c n))
    with
    L := adaptiveL c n
    hL_pos := adaptiveL_pos c n
    R := admR n
    hR_pos := admR_pos n

    diagonalSpikeActive :=
      fun k => k ∈ admStageCodes n

    diagonalSpikeContribution :=
      fun k => (ppDecode k).weightC

    canonicalSpikeContribution :=
      fun k => (ppDecode k).weightC

    h_diagonalSpikeExtraction := by
      intro k _
      rfl

    diagonalSpikeActiveIndices :=
      admStageCodes n

    h_diagonalSpikeActiveIndices_active := by
      intro k hk
      exact hk

    h_diagonalSpikeActiveIndices_complete := by
      intro k hk
      exact hk

    diagonalSpikeToPP :=
      ppDecode

    h_diagonalSpikeToPP_inj := by
      intro a _ b _ h
      have h2 := congrArg ppCode h
      simpa [ppCode_ppDecode] using h2

    h_canonicalSpikeContribution_eq_weightC := by
      intro k _
      rfl

    h_diagonalSpikeToPP_center_le_R := by
      intro k hk
      rcases mem_admStageCodes.mp hk with ⟨q, hq, rfl⟩
      have hfil := Finset.mem_filter.mp hq
      have hcenter := hfil.2.2
      simpa [ppDecode_ppCode] using hcenter

    h_diagonalSpikeToPP_complete_center_le_R := by
      intro q hq hle
      have hbelow :
          q ∈ concretePrimePowerBelowCutoff (admR n) :=
        concretePrimePowerEnum.h_mem_belowCutoff
          (admR n) q hq hle
      refine ⟨ppCode q, ?_, ppDecode_ppCode q⟩
      exact mem_admStageCodes.mpr
        ⟨q, hbelow, rfl⟩

    appendixDFiniteFStage :=
      fun s =>
        adaptiveDensityC c n *
          decodedGalerkinPerturbedFStage
            (N := adaptiveN c n)
            (galerkinFreeMu
              (adaptiveN c n)
              (adaptiveL c n))
            1
            (activePrimePowerCodesCenterBelow
              (admR n))
            ppWeightReal
            (adaptiveL c n)
            s }

/-- The decoded adaptive stage carries the adaptive window. -/
theorem decodedAdaptiveGalerkinStageSeq_L
    (c : ℝ) (n : ℕ) :
    (decodedAdaptiveGalerkinStageSeq c n).L
      = adaptiveL c n :=
  rfl

/-- The decoded adaptive stage retains the same cutoff. -/
theorem decodedAdaptiveGalerkinStageSeq_R
    (c : ℝ) (n : ℕ) :
    (decodedAdaptiveGalerkinStageSeq c n).R
      = admR n :=
  rfl

/-- The B-stage is unchanged because it depends only on the cutoff. -/
theorem decodedAdaptiveGalerkinStage_B_stage_eq
    (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage
        (decodedAdaptiveGalerkinStageSeq c n) s
      =
    galerkinStagePackage.B_stage
        (admissibleGalerkinStageSeq n) s :=
  rfl

/-- F-slot unfold for the decoded adaptive stage. -/
theorem decodedAdaptiveGalerkinStageSeq_F_stage
    (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.F_stage
        (decodedAdaptiveGalerkinStageSeq c n) s
      =
    adaptiveDensityC c n *
      decodedGalerkinPerturbedFStage
        (N := adaptiveN c n)
        (galerkinFreeMu
          (adaptiveN c n)
          (adaptiveL c n))
        1
        (activePrimePowerCodesCenterBelow
          (admR n))
        ppWeightReal
        (adaptiveL c n)
        (s + (SupVConst : ℂ)) :=
  rfl

#print axioms decodedAdaptiveGalerkinStageSeq
#print axioms decodedAdaptiveGalerkinStageSeq_L
#print axioms decodedAdaptiveGalerkinStageSeq_R
#print axioms decodedAdaptiveGalerkinStage_B_stage_eq
#print axioms decodedAdaptiveGalerkinStageSeq_F_stage

end

end RHFormalization
