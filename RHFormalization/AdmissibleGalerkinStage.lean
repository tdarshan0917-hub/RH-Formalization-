import RHFormalization.GalerkinStageSequence
import RHFormalization.GalerkinStagePackage

/-!
# RHFormalization.AdmissibleGalerkinStage

**THE ADMISSIBLE NET (skeleton).** The manuscript-faithful coupled cutoff
sequence (L_n, R_n) with density-normalized F-slot, feeding the UNCHANGED
`galerkinStagePackage`. Replaces the fixed-window `galerkinStageSeq` as the
final exhaustion for both fronts.

Schedule (re-tunable one-liners):
  admR n = log(n+2)/2   (SLOW prime cutoff — elementary S₁ ≤ R·e^R residual
                         estimate closes; hB via the slow-cutoff engine)
  admL n = (n + 2)³     (window; D.ADM headroom M(R_n)/(2L_n) ≤ 1 to be
                         proven as a named theorem later)
  admN n = (n + 2)⁴     (Galerkin dimension; admN/admL → ∞)

Shift: the banked L-generic `galerkinStageShift` (Classical.choose of
`exists_shift_making_galerkin_nonneg`) — NOT SupVConst, whose uniform bound
is pinned to the L = 1 box.

This file makes NO analytic claims. Obligations to be discharged against
this sequence in later files: D.ADM anchor bound, density-normalized F-data
(DFHLimitData), R-data via D.LOC/D.DISP/D.TAIL (DMasterResidualData).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- Prime-power cutoff schedule: same as the fixed route. -/
def admR (n : ℕ) : ℝ := Real.log ((n : ℝ) + 2) / 2

/-- Window schedule: polynomial growth. -/
def admL (n : ℕ) : ℝ := ((n : ℝ) + 2) ^ 3

/-- Galerkin dimension schedule: grows strictly faster than the window. -/
def admN (n : ℕ) : ℕ := (n + 2) ^ 4

theorem admR_pos (n : ℕ) : 0 < admR n := by
  unfold admR
  have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlog : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos h2
  linarith

/-- The slow cutoff still tends to infinity — the only property the
slow-cutoff B-convergence engine needs. -/
theorem tendsto_admR_atTop :
    Filter.Tendsto admR Filter.atTop Filter.atTop := by
  have h0 : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := by
    first
      | exact tendsto_natCast_atTop_atTop
      | exact tendsto_nat_cast_atTop_atTop
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 2 h0
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h1
  unfold admR
  first
    | exact h2.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    | · have h3 : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2) * (1 / 2))
            Filter.atTop Filter.atTop :=
          h2.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)
        refine h3.congr (fun n => ?_)
        ring

theorem admL_pos (n : ℕ) : 0 < admL n := by unfold admL; positivity

theorem admL_ge_one (n : ℕ) : 1 ≤ admL n := by
  unfold admL
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [h1, h0, sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 1),
    mul_nonneg (mul_nonneg h0 h0) h0]

/-- The density-normalization constant at stage n, as a complex scalar. -/
def admDensityC (n : ℕ) : ℂ := ((1 / (2 * admL n) : ℝ) : ℂ)

/-- Spike code set at the slow cutoff `admR n` (mirrors `ppStageCodes`). -/
def admStageCodes (n : ℕ) : Finset ℕ :=
  (concretePrimePowerBelowCutoff (admR n)).image ppCode

theorem mem_admStageCodes {n k : ℕ} :
    k ∈ admStageCodes n ↔
      ∃ q ∈ concretePrimePowerBelowCutoff (admR n), ppCode q = k := by
  simp [admStageCodes]

/-- **THE ADMISSIBLE STAGE SEQUENCE.** The genuine galerkin operator stage at
window `admL n`, dimension `admN n`, codes below `admR n`, with the stage's
own L-generic nonnegativity shift, the `.L` field set to the true window, and
the F-slot carrying the manuscript's density normalization `1/(2L_n)`. -/
def admissibleGalerkinStageSeq (n : ℕ) : DFiniteStage :=
  { galerkinOperatorDFiniteStage_ofShift (N := admN n) n
      (galerkinFreeMu (admN n) (admL n))
      1
      (activePrimePowerCodesCenterBelow (admR n))
      ppWeightReal
      (admL n)
      (galerkinStageShift (admN n) (galerkinFreeMu (admN n) (admL n)) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
      (galerkinStageShift_spec (admN n) (galerkinFreeMu (admN n) (admL n)) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
    with
    L := admL n
    hL_pos := admL_pos n
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
      intro k hk
      rcases mem_admStageCodes.mp hk with ⟨q, hq, rfl⟩
      have hfil := Finset.mem_filter.mp hq
      have hcenter := hfil.2.2
      simpa [ppDecode_ppCode] using hcenter
    h_diagonalSpikeToPP_complete_center_le_R := by
      intro q hq hle
      have hbelow : q ∈ concretePrimePowerBelowCutoff (admR n) :=
        concretePrimePowerEnum.h_mem_belowCutoff (admR n) q hq hle
      refine ⟨ppCode q, ?_, ppDecode_ppCode q⟩
      exact mem_admStageCodes.mpr ⟨q, hbelow, rfl⟩
    appendixDFiniteFStage := fun s =>
      admDensityC n *
        galerkinPerturbedFStage (N := admN n)
          (galerkinFreeMu (admN n) (admL n)) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (admL n) s }

/-- The admissible stage carries the true window. -/
theorem admissibleGalerkinStageSeq_L (n : ℕ) :
    (admissibleGalerkinStageSeq n).L = admL n := rfl

/-- The admissible stage's prime cutoff is the schedule knob `admR`. -/
theorem admissibleGalerkinStageSeq_R (n : ℕ) :
    (admissibleGalerkinStageSeq n).R = admR n := rfl

/-- F-slot unfold at the stage level: density-normalized genuine trace. -/
theorem admissibleGalerkinStageSeq_F_stage (n : ℕ) :
    (admissibleGalerkinStageSeq n).appendixDFiniteFStage
      = fun s =>
          admDensityC n *
            galerkinPerturbedFStage (N := admN n)
              (galerkinFreeMu (admN n) (admL n)) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (admL n) s := rfl

/-- **Package F-slot at the admissible stage** (the object Front F converges):
the density-normalized shifted trace. -/
theorem galerkinStagePackage_F_at_admissible (n : ℕ) (s : ℂ) :
    galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      = admDensityC n *
          galerkinPerturbedFStage (N := admN n)
            (galerkinFreeMu (admN n) (admL n)) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (admL n) (s + (SupVConst : ℂ)) := rfl

/-- **Package B-slot at the admissible stage**: the SAME canonical finite
prime package as the fixed route (cutoff unchanged) — `galerkin_hB`
machinery transfers. -/
theorem galerkinStagePackage_B_at_admissible (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (admR n))
          shiftedLaplaceHeatKernelC s := rfl

#print axioms admissibleGalerkinStageSeq
#print axioms admissibleGalerkinStageSeq_L
#print axioms admissibleGalerkinStageSeq_R
#print axioms admissibleGalerkinStageSeq_F_stage
#print axioms galerkinStagePackage_F_at_admissible
#print axioms galerkinStagePackage_B_at_admissible

end

end RHFormalization
