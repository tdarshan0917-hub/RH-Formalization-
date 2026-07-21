-- SENTINEL: SECT-v2
import RHFormalization.AdaptiveCombinedFreeR
import RHFormalization.AdaptivePrimeSplitObjects
import RHFormalization.DMRSectorTimeSplit
import RHFormalization.AdaptiveCombinedSectorAssembly
import Mathlib

/-!
# AdaptiveSectorObjects v2 — Ω-honest sectors + exact h_decomp

REVISION v1→v2: v1's Tail := canonicalPackageTail is a divergent integral
(junk 0) for Re s ≤ −1/4, hence meaningless on general Ω-compacts. v2 uses
the Ω-native split: Short := canonicalPackageShort (FINITE-time integral,
converges ∀ s ∈ ℂ); CompTail := (B − M) − Short (the compensated tail —
equals canonicalPackageTail − M on Re s > 0 by the banked D.MR.3 split).
M stays paired with the divergent side, per the frozen B−M rule.

ROW STATUS (the whole campaign):
  Short   — provable NOW: Gaussian-in-log-q, n-uniform (P_c mechanism).
  CompTail— KNIFE-EDGE: Duhamel/word route only, never arithmetic.
  Disp    — banked-species clone (SecondResolventResidual ancestor).
  Window  — banked-species clone (FirstOrderWindow ancestor).
This file banks ONLY the decomposition row. Decomposition ≠ bounds.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **Short sector**: finite-time package head — an integral over
`(0,t0]`, hence a well-defined (entire-in-`s`) object for EVERY `s`. -/
def adaptiveSectorShort (t0 : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  canonicalPackageShort (activePrimePowerPairsCenterBelow (admR n)) t0 s

/-- **Compensated-tail sector** (the knife-edge): the compensated package
minus the short head. On `Re s > 0` this equals
`canonicalPackageTail − compensatorM` (banked D.MR.3 split). -/
def adaptiveSectorCompTail (c t0 : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
      - compensatorM n s)
    - adaptiveSectorShort t0 n s

/-- Window sector: minus the adaptive first-order window. -/
def adaptiveSectorWindow (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  - adaptiveFirstOrderWindow c n s

/-- Displacement/residual sector: minus the adaptive second resolvent
residual. -/
def adaptiveSectorDisp (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  - adaptiveSecondResolventResidual c n s

/-- **THE EXACT SECTOR DECOMPOSITION** — h_decomp on all of Ω, pure
algebra; every summand is a genuinely-defined Ω object. -/
theorem adaptiveCombinedFreeR_eq_sector_sum
    (c t0 : ℝ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    adaptiveCombinedFreeR c n s
      = adaptiveSectorShort t0 n s
        + adaptiveSectorDisp c n s
        + adaptiveSectorCompTail c t0 n s
        + adaptiveSectorWindow c n s := by
  have hcomb : adaptiveCombinedFreeR c n s
      = (galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
            - compensatorM n s)
          - adaptiveShortResidual c n s :=
    adaptiveCombinedFreeR_eq c n hs
  rw [hcomb]
  unfold adaptiveSectorCompTail adaptiveSectorShort adaptiveSectorDisp
    adaptiveSectorWindow adaptiveShortResidual
  ring

/-- h_decomp in the combiner's exact quantifier shape. -/
theorem adaptive_sector_decomp (c t0 : ℝ) :
    ∀ n : ℕ, ∀ s : ℂ, s ∈ Ω →
      adaptiveCombinedFreeR c n s
        = adaptiveSectorShort t0 n s
          + adaptiveSectorDisp c n s
          + adaptiveSectorCompTail c t0 n s
          + adaptiveSectorWindow c n s :=
  fun n s hs => adaptiveCombinedFreeR_eq_sector_sum c t0 n hs

/-- **The gate with Ω-honest sectors**: four bounds ⟹
DBFFO3CompensatedBBound. These four hypotheses are the entire remaining
campaign on this route. -/
theorem adaptive_compensatedB_bounded_of_sector_bounds
    (c t0 : ℝ)
    (h_short_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cl : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorShort t0 n s‖ ≤ Cl)
    (h_disp_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cd : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorDisp c n s‖ ≤ Cd)
    (h_ctail_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Ct : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorCompTail c t0 n s‖ ≤ Ct)
    (h_window_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cw : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorWindow c n s‖ ≤ Cw)
    (HshortA : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cs : ℝ, ∀ n : ℕ, ∀ s ∈ K,
          ‖adaptiveShortResidual c n s‖ ≤ Cs) :
    DBFFO3CompensatedBBound :=
  adaptive_compensatedB_bounded_from_four_sectors c
    (fun n s => adaptiveSectorShort t0 n s)
    (fun n s => adaptiveSectorDisp c n s)
    (fun n s => adaptiveSectorCompTail c t0 n s)
    (fun n s => adaptiveSectorWindow c n s)
    (adaptive_sector_decomp c t0)
    h_short_le h_disp_le h_ctail_le h_window_le HshortA

#print axioms adaptiveCombinedFreeR_eq_sector_sum
#print axioms adaptive_sector_decomp
#print axioms adaptive_compensatedB_bounded_of_sector_bounds

end

end RHFormalization
