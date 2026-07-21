-- SENTINEL: SECT-v1
import RHFormalization.AdaptiveCombinedFreeR
import RHFormalization.AdaptivePrimeSplitObjects
import RHFormalization.DMRSectorTimeSplit
import RHFormalization.AdaptiveCombinedSectorAssembly
import Mathlib

/-!
# AdaptiveSectorObjects — the CONCRETE four sectors + exact h_decomp

ROUTE CARD
1. Consumer: `adaptive_combined_bound_from_four_sectors` (banked) →
   `adaptive_compensatedB_bounded_from_four_sectors` → DBFFO3CompensatedBBound.
2. This file banks EXACTLY ONE row: h_decomp, on all of Ω, algebraically.
   The four bound rows (Loc/Disp/Tail/Window) are NOT touched here and
   remain the open campaign. No mirage claim: decomposition ≠ bounds.
3. Design: Loc := (B − M) − Tail, so the package time-split (half-plane
   only) is NOT needed for the identity; on Re s > 0, Loc = pkgShort − M.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- Tail sector at the adaptive stage: the banked package tail (active
set depends only on `admR n`, shared with the admissible net). -/
def adaptiveSectorTail (t0 : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) t0 s

/-- Window sector: minus the adaptive first-order window. -/
def adaptiveSectorWindow (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  - adaptiveFirstOrderWindow c n s

/-- Displacement/residual sector: minus the adaptive second resolvent
residual. -/
def adaptiveSectorDisp (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  - adaptiveSecondResolventResidual c n s

/-- **Local/bulk sector** (the knife-edge): compensated package minus
the tail. On the Laplace half-plane this equals `packageShort − M`. -/
def adaptiveSectorLoc (c t0 : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
      - compensatorM n s)
    - adaptiveSectorTail t0 n s

/-- **THE EXACT SECTOR DECOMPOSITION** — h_decomp for the banked
four-sector combiner, on all of Ω, pure algebra. -/
theorem adaptiveCombinedFreeR_eq_sector_sum
    (c t0 : ℝ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    adaptiveCombinedFreeR c n s
      = adaptiveSectorLoc c t0 n s
        + adaptiveSectorDisp c n s
        + adaptiveSectorTail t0 n s
        + adaptiveSectorWindow c n s := by
  have hcomb : adaptiveCombinedFreeR c n s
      = (galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
            - compensatorM n s)
          - adaptiveShortResidual c n s := by
    first
      | exact adaptiveCombinedFreeR_eq c n hs
      | (rw [adaptiveCombinedFreeR_eq c n hs])
      | (rw [adaptiveCombinedFreeR_eq c n hs]
         first
           | rfl
           | (unfold adaptiveCompensatedB adaptiveShortResidual; ring)
           | (unfold adaptiveCompensatedBFamily adaptiveShortResidual; ring)
           | (unfold compensatedBFamily adaptiveShortResidual; ring)
           | ring)
      | (rw [adaptiveCombinedFreeR_eq c n s hs])
      | (rw [adaptiveCombinedFreeR_eq c n s hs]; ring)
  rw [hcomb]
  unfold adaptiveSectorLoc adaptiveSectorDisp adaptiveSectorTail
    adaptiveSectorWindow adaptiveShortResidual
  ring

/-- h_decomp in the combiner's exact quantifier shape. -/
theorem adaptive_sector_decomp (c t0 : ℝ) :
    ∀ n : ℕ, ∀ s : ℂ, s ∈ Ω →
      adaptiveCombinedFreeR c n s
        = adaptiveSectorLoc c t0 n s
          + adaptiveSectorDisp c n s
          + adaptiveSectorTail t0 n s
          + adaptiveSectorWindow c n s :=
  fun n s hs => adaptiveCombinedFreeR_eq_sector_sum c t0 n hs

/-- **The gate, restated with concrete sectors**: four bounds ⟹
DBFFO3CompensatedBBound. The four hypotheses are the ENTIRE remaining
campaign; nothing else is open on this route. -/
theorem adaptive_compensatedB_bounded_of_sector_bounds
    (c t0 : ℝ)
    (h_loc_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cl : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorLoc c t0 n s‖ ≤ Cl)
    (h_disp_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cd : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorDisp c n s‖ ≤ Cd)
    (h_tail_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Ct : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorTail t0 n s‖ ≤ Ct)
    (h_window_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cw : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorWindow c n s‖ ≤ Cw)
    (HshortA : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cs : ℝ, ∀ n : ℕ, ∀ s ∈ K,
          ‖adaptiveShortResidual c n s‖ ≤ Cs) :
    DBFFO3CompensatedBBound :=
  adaptive_compensatedB_bounded_from_four_sectors c
    (fun n s => adaptiveSectorLoc c t0 n s)
    (fun n s => adaptiveSectorDisp c n s)
    (fun n s => adaptiveSectorTail t0 n s)
    (fun n s => adaptiveSectorWindow c n s)
    (adaptive_sector_decomp c t0)
    h_loc_le h_disp_le h_tail_le h_window_le HshortA

#print axioms adaptiveCombinedFreeR_eq_sector_sum
#print axioms adaptive_sector_decomp
#print axioms adaptive_compensatedB_bounded_of_sector_bounds

end

end RHFormalization
