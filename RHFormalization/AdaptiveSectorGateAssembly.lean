-- SENTINEL: GATE-v1
import RHFormalization.AdaptiveSectorObjects
import RHFormalization.AdaptiveShortSectorBound
import RHFormalization.AdaptiveFirstOrderVanish
import RHFormalization.AdaptiveResidualUniform
import Mathlib

/-!
# AdaptiveSectorGateAssembly — three rows wired; ONE hypothesis remains

Wires the banked Short (SHORT-v3), Window (AFOW-v1), Disp (ARES-v1) rows
plus HshortA (from Window+Disp) into the SECT-v2 combiner. Conclusion:
DBFFO3CompensatedBBound from EXACTLY ONE open input — h_ctail_le, the
CompTail knife-edge. This file is wiring only; the knife-edge is NOT
discharged here and remains the entire open campaign.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- Window row in the combiner's shape (from banked C/(n+2) decay). -/
theorem adaptiveSectorWindow_loc_bdd (c : ℝ) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Cw : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorWindow c n s‖ ≤ Cw := by
  intro K hK hKO
  obtain ⟨C, hCpos, hC⟩ := adaptiveFirstOrderWindow_uniform_bound c K hK hKO
  refine ⟨C / 2, ?_⟩
  intro n s hs
  have h1 : ‖adaptiveSectorWindow c n s‖ = ‖adaptiveFirstOrderWindow c n s‖ := by
    unfold adaptiveSectorWindow
    exact norm_neg _
  rw [h1]
  refine le_trans (hC n s hs) ?_
  have hn2 : (2:ℝ) ≤ (n:ℝ) + 2 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  exact div_le_div_of_nonneg_left hCpos.le (by norm_num) hn2

/-- Disp row in the combiner's shape. -/
theorem adaptiveSectorDisp_loc_bdd (c : ℝ) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Cd : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorDisp c n s‖ ≤ Cd := by
  intro K hK hKO
  obtain ⟨C, _, hC⟩ := adaptiveSecondResolventResidual_uniform_bound c K hK hKO
  refine ⟨C, ?_⟩
  intro n s hs
  have h1 : ‖adaptiveSectorDisp c n s‖
      = ‖adaptiveSecondResolventResidual c n s‖ := by
    unfold adaptiveSectorDisp
    exact norm_neg _
  rw [h1]
  exact hC n s hs

/-- HshortA from the two banked rows (triangle inequality). -/
theorem adaptiveShortResidual_loc_bdd (c : ℝ) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Cs : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveShortResidual c n s‖ ≤ Cs := by
  intro K hK hKO
  obtain ⟨Cw, hCwpos, hCw⟩ := adaptiveFirstOrderWindow_uniform_bound c K hK hKO
  obtain ⟨Cd, _, hCd⟩ := adaptiveSecondResolventResidual_uniform_bound c K hK hKO
  refine ⟨Cw / 2 + Cd, ?_⟩
  intro n s hs
  unfold adaptiveShortResidual
  refine le_trans (norm_add_le _ _) ?_
  have hw : ‖adaptiveFirstOrderWindow c n s‖ ≤ Cw / 2 := by
    refine le_trans (hCw n s hs) ?_
    have hn2 : (2:ℝ) ≤ (n:ℝ) + 2 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact div_le_div_of_nonneg_left hCwpos.le (by norm_num) hn2
  have hd := hCd n s hs
  linarith

/-- **THE GATE, one input**: CompTail bound ⟹ DBFFO3CompensatedBBound.
The hypothesis h_ctail_le is the ENTIRE remaining open campaign. -/
theorem adaptive_compensatedB_bounded_of_ctail
    (c t0 : ℝ) (ht0 : 0 < t0)
    (h_ctail_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Ct : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorCompTail c t0 n s‖ ≤ Ct) :
    DBFFO3CompensatedBBound :=
  adaptive_compensatedB_bounded_of_sector_bounds c t0
    (adaptiveSectorShort_loc_bdd t0 ht0)
    (adaptiveSectorDisp_loc_bdd c)
    h_ctail_le
    (adaptiveSectorWindow_loc_bdd c)
    (adaptiveShortResidual_loc_bdd c)

#print axioms adaptiveSectorWindow_loc_bdd
#print axioms adaptiveSectorDisp_loc_bdd
#print axioms adaptiveShortResidual_loc_bdd
#print axioms adaptive_compensatedB_bounded_of_ctail

end

end RHFormalization
