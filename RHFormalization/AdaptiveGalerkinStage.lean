import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.DecodedAnchorDischarge
import RHFormalization.GalerkinStagePackage
import Mathlib

/-!
# AdaptiveGalerkinStage — the D.ADM-NET ordered cutoff net

Lemma D.ADM-NET: fix `R_n = admR n`, note `M(R_n) < ∞` (banked), THEN choose
the window `adaptiveL c n := max (admL n) (M(R_n))` — D.ADM holds BY
CONSTRUCTION (`adaptiveGalerkinStage_DADM`), and `admL n ≤ adaptiveL c n`
preserves every banked lower bound on the window.

RESOLUTION REPAIR: since `M(R)` is super-polynomial, keeping `admN = (n+2)⁴`
would collapse `N/L → 0` and lose the Galerkin spectral ceiling. The
dimension is therefore also adaptive:
  `adaptiveN c n := max (admN n) ⌈adaptiveL c n · (n+2)⌉₊`,
restoring the schedule's resolution ratio `N/L ≥ n+2`
(`adaptiveL_mul_le_adaptiveN`) while keeping `admN n ≤ adaptiveN c n`.

Unchanged: cutoff `admR n`, active codes, spike fields, `compensatorM`
(a cutoff-only object). `B_stage` reads only `.R`, so the adaptive and
admissible B-stages agree definitionally (`adaptiveGalerkinStage_B_stage_eq`).

Parametric in the coupling `c` (the manuscript's absolute `C*·t0`).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- The stage anchor `M(admR n)` at coupling `c` (live δ = 1). -/
def adaptiveAnchor (c : ℝ) (n : ℕ) : ℝ :=
  decodedAdmissibleLocalAnchor 1 (admR n) c

/-- **The D.ADM-NET adaptive window**: fix R, then take L large enough. -/
def adaptiveL (c : ℝ) (n : ℕ) : ℝ :=
  max (admL n) (adaptiveAnchor c n)

theorem admL_le_adaptiveL (c : ℝ) (n : ℕ) : admL n ≤ adaptiveL c n :=
  le_max_left _ _

theorem adaptiveL_pos (c : ℝ) (n : ℕ) : 0 < adaptiveL c n :=
  lt_of_lt_of_le (admL_pos n) (admL_le_adaptiveL c n)

theorem adaptiveL_ge_one (c : ℝ) (n : ℕ) : 1 ≤ adaptiveL c n :=
  (admL_ge_one n).trans (admL_le_adaptiveL c n)

/-- **D.ADM HOLDS BY CONSTRUCTION on the adaptive net**:
`M(R_n)/(2·L_n) ≤ 1` for every stage, at any coupling `c ≥ 0`. -/
theorem adaptiveGalerkinStage_DADM (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    adaptiveAnchor c n / (2 * adaptiveL c n) ≤ 1 := by
  unfold adaptiveL adaptiveAnchor
  exact decodedAnchor_window_bound_live (admR n) c (admL n) hc (admL_ge_one n)

/-- **The adaptive Galerkin dimension**: scales with the adaptive window so
the exhaustion stays spectrally resolved. -/
def adaptiveN (c : ℝ) (n : ℕ) : ℕ :=
  max (admN n) ⌈adaptiveL c n * ((n : ℝ) + 2)⌉₊

theorem admN_le_adaptiveN (c : ℝ) (n : ℕ) : admN n ≤ adaptiveN c n :=
  le_max_left _ _

/-- **Resolution restored**: `adaptiveN / adaptiveL ≥ n + 2`, stated
division-free. The schedule's load-bearing density ratio survives the
adaptive window. -/
theorem adaptiveL_mul_le_adaptiveN (c : ℝ) (n : ℕ) :
    adaptiveL c n * ((n : ℝ) + 2) ≤ (adaptiveN c n : ℝ) := by
  have h1 : adaptiveL c n * ((n : ℝ) + 2)
      ≤ (⌈adaptiveL c n * ((n : ℝ) + 2)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ⌈adaptiveL c n * ((n : ℝ) + 2)⌉₊ ≤ adaptiveN c n :=
    le_max_right (admN n) _
  exact h1.trans (Nat.cast_le.mpr h2)

theorem adaptiveN_pos (c : ℝ) (n : ℕ) : 0 < adaptiveN c n :=
  lt_of_lt_of_le (by unfold admN; positivity) (admN_le_adaptiveN c n)

/-- Density normalization at the adaptive window. -/
def adaptiveDensityC (c : ℝ) (n : ℕ) : ℂ :=
  ((1 / (2 * adaptiveL c n) : ℝ) : ℂ)

/-- **THE ADAPTIVE STAGE SEQUENCE.** Identical to
`admissibleGalerkinStageSeq` except window `adaptiveL c n` and dimension
`adaptiveN c n`; cutoff, codes, and spike fields unchanged. -/
def adaptiveGalerkinStageSeq (c : ℝ) (n : ℕ) : DFiniteStage :=
  { galerkinOperatorDFiniteStage_ofShift (N := adaptiveN c n) n
      (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
      1
      (activePrimePowerCodesCenterBelow (admR n))
      ppWeightReal
      (adaptiveL c n)
      (galerkinStageShift (adaptiveN c n)
        (galerkinFreeMu (adaptiveN c n) (adaptiveL c n)) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (adaptiveL c n))
      (galerkinStageShift_spec (adaptiveN c n)
        (galerkinFreeMu (adaptiveN c n) (adaptiveL c n)) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (adaptiveL c n))
    with
    L := adaptiveL c n
    hL_pos := adaptiveL_pos c n
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
      adaptiveDensityC c n *
        galerkinPerturbedFStage (N := adaptiveN c n)
          (galerkinFreeMu (adaptiveN c n) (adaptiveL c n)) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (adaptiveL c n) s }

/-- The adaptive stage carries the adaptive window. -/
theorem adaptiveGalerkinStageSeq_L (c : ℝ) (n : ℕ) :
    (adaptiveGalerkinStageSeq c n).L = adaptiveL c n := rfl

/-- The adaptive stage keeps the SAME prime cutoff as the admissible net. -/
theorem adaptiveGalerkinStageSeq_R (c : ℝ) (n : ℕ) :
    (adaptiveGalerkinStageSeq c n).R = admR n := rfl

/-- **THE CHEAP BRIDGE.** `B_stage` reads only `.R`, and both nets carry
`admR n` — the canonical B-side is IDENTICAL on the two nets; compensated-B,
star-object, and O3 layers need no modification. -/
theorem adaptiveGalerkinStage_B_stage_eq (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s =
      galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := rfl

/-- F-slot unfold on the adaptive net. -/
theorem adaptiveGalerkinStageSeq_F_stage (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.F_stage (adaptiveGalerkinStageSeq c n) s =
      adaptiveDensityC c n *
        galerkinPerturbedFStage (N := adaptiveN c n)
          (galerkinFreeMu (adaptiveN c n) (adaptiveL c n)) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (adaptiveL c n) (s + (SupVConst : ℂ)) := rfl

#print axioms adaptiveGalerkinStage_DADM
#print axioms adaptiveL_mul_le_adaptiveN
#print axioms adaptiveN_pos
#print axioms adaptiveGalerkinStageSeq
#print axioms adaptiveGalerkinStage_B_stage_eq
#print axioms adaptiveGalerkinStageSeq_F_stage

end

end RHFormalization
