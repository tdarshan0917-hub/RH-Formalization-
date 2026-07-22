-- SENTINEL: B2CONN-v3
import RHFormalization.AdaptiveSectorObjects
import RHFormalization.AdaptiveShortSectorBound
import RHFormalization.DecodedCanonicalSectorDecomposition
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.AdaptiveDefectLocBdd
import RHFormalization.DecodedWindowCorrectionBound
import Mathlib

/-!
# B2OneLetterConnector — the one-letter cancellation, compiled

B_stage = 2·(one-letter transform) − 2·defect + windowCorrection
(pure algebra: defect definition + package_sub_two_windowed_eq_correction).
Hence CompTail = bulkSeam − 2·defect + windowCorr − packageShort, and
h_ctail_le follows from a BULK SEAM bound alone (three other terms banked:
defect loc_bdd, window correction uniform, Short row SHORT-v3).

TRAP CHECK (rule 5): the residue `decodedBulkSeam = 2·FreePaired − M` is
the SAME hard core — SeamStarUnification proves seam = (2√(s+1/4))⁻¹·
starObject, off-parabola banked, at parabola depth OPEN. This file does NOT
shrink the obstruction; it compiles the reduction and discharges the
arithmetic side. Residue belongs to the manuscript BULK sector (B6/P2),
NOT to D.LOC.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **THE ONE-LETTER IDENTITY**: B_stage in terms of the one-letter word
transform, the banked defect, and the window correction. -/
theorem adaptive_B_stage_eq_oneLetter (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
      = 2 * adaptiveFreePairedTransform c n s
        - 2 * adaptiveGalerkinTransformDefect c n s
        + decodedWindowCorrection c n s := by
  have hL : adaptiveL c n ≠ 0 := (adaptiveL_pos c n).ne'
  have hpkg := package_sub_two_windowed_eq_correction c n s hL
  have hdef : adaptiveGalerkinTransformDefect c n s
      = adaptiveFreePairedTransform c n s
        - windowedCanonicalPackage
            (activePrimePowerPairsCenterBelow (admR n)) (adaptiveL c n)
            shiftedLaplaceHeatKernelC s := rfl
  have hB : galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
      = finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (admR n))
          shiftedLaplaceHeatKernelC s := by
    first
      | rfl
      | (rw [adaptiveGalerkinStage_B_stage_eq c n s]; rfl)
      | (rw [adaptiveGalerkinStage_B_stage_eq]; rfl)
  rw [hB, hdef]
  linear_combination hpkg

/-- **CompTail in seam form.** -/
theorem adaptiveSectorCompTail_eq_seam_form (c t0 : ℝ) (n : ℕ) (s : ℂ) :
    adaptiveSectorCompTail c t0 n s
      = decodedBulkSeam c n s
        - 2 * adaptiveGalerkinTransformDefect c n s
        + decodedWindowCorrection c n s
        - adaptiveSectorShort t0 n s := by
  unfold adaptiveSectorCompTail decodedBulkSeam
  rw [adaptive_B_stage_eq_oneLetter c n s]
  ring

/-- **h_ctail_le from a BULK SEAM bound alone.** The other three terms are
banked. This is the sharpest compiled form of the frontier. -/
theorem h_ctail_le_of_seam_bdd (c t0 : ℝ) (ht0 : 0 < t0)
    (h_seam : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cs : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖decodedBulkSeam c n s‖ ≤ Cs) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Ct : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorCompTail c t0 n s‖ ≤ Ct := by
  intro K hK hKO
  obtain ⟨Cs, hCs⟩ := h_seam K hK hKO
  obtain ⟨Cd, hCd⟩ : ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖adaptiveGalerkinTransformDefect c n s‖ ≤ C := by
    first
      | exact adaptiveGalerkinTransformDefect_loc_bdd c K hKO hK
      | exact adaptiveGalerkinTransformDefect_loc_bdd c K hK hKO
  obtain ⟨Cw, _, hCw⟩ := decodedWindowCorrection_uniform_bound c K hK hKO
  obtain ⟨Csh, hCsh⟩ := adaptiveSectorShort_loc_bdd t0 ht0 K hK hKO
  refine ⟨Cs + 2 * Cd + Cw + Csh, ?_⟩
  intro n s hs
  rw [adaptiveSectorCompTail_eq_seam_form c t0 n s]
  have h1 := hCs n s hs
  have h2 := hCd n s hs
  have h3 := hCw n s hs
  have h4 := hCsh n s hs
  have hd2 : ‖(2:ℂ) * adaptiveGalerkinTransformDefect c n s‖ ≤ 2 * Cd := by
    rw [norm_mul]
    have hn2 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [hn2]
    linarith
  have hsplit : ∀ a b c d : ℂ, ‖a - b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have he : a - b + c - d = a + (-b) + c + (-d) := by ring
    rw [he]
    have t1 : ‖a + (-b) + c + (-d)‖ ≤ ‖a + (-b) + c‖ + ‖(-d)‖ := norm_add_le _ _
    have t2 : ‖a + (-b) + c‖ ≤ ‖a + (-b)‖ + ‖c‖ := norm_add_le _ _
    have t3 : ‖a + (-b)‖ ≤ ‖a‖ + ‖(-b)‖ := norm_add_le _ _
    have hb : ‖(-b)‖ = ‖b‖ := norm_neg b
    have hd : ‖(-d)‖ = ‖d‖ := norm_neg d
    rw [hb] at t3
    rw [hd] at t1
    linarith
  have hfin := hsplit (decodedBulkSeam c n s)
    ((2:ℂ) * adaptiveGalerkinTransformDefect c n s)
    (decodedWindowCorrection c n s) (adaptiveSectorShort t0 n s)
  linarith

#print axioms adaptive_B_stage_eq_oneLetter
#print axioms adaptiveSectorCompTail_eq_seam_form
#print axioms h_ctail_le_of_seam_bdd

end

end RHFormalization
