import RHFormalization.FourSectorAccounting
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-!
# ManuscriptSectorCorrespondence — D.MR.3 vs the machine, sectors independent

Manuscript assignments (D.MR.1/3, verbatim construction):
  short+win : ALL short-time canonical content  ↦ galHead   (t ≤ t₀ integral — independent def)
  tail      : large-time density contribution   ↦ galFTailClosed (Step-3's exact spectral object)
  bulk      : classical/background corrections  ↦ Bcorr (BcorrWin + compensatorM — the
              subtracted classical transforms, independent def)
No sector is defined by subtraction from Rcan. The machine equality then
forces the exact difference from D.MR.3's claimed exhaustive RHS.
-/

/-- **SECTOR CORRESPONDENCE (exact, Re s > 0)**: the canonical residual is
the manuscript sectors MINUS the large-time one-letter prime tail. -/
theorem Rcan_eq_manuscript_sectors_sub_Btail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    canonicalRcanStage n s
      = galHead n s + galFTailClosed n s + Bcorr n s - galBTail n s := by
  have h1 := canonicalRcanStage_eq_head_add_Ftail_add_obstruction n s hs
  have h2 := canonicalTailObstruction_eq_Bcorr_sub_Btail n s hs
  rw [h1, h2]
  ring

/-- **THE EXACT DIFFERENCE from D.MR.3's exhaustive claim**: with every
manuscript sector filled independently, the leftover is `−galBTail`;
in paired coordinates (classical density leg regrouped into bulk), the
leftover is exactly `pairedTailGap`. -/
theorem manuscript_RHS_difference (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (galHead n s + galFTailClosed n s + Bcorr n s) - canonicalRcanStage n s
      = galBTail n s := by
  rw [Rcan_eq_manuscript_sectors_sub_Btail n s hs]
  ring

#print axioms Rcan_eq_manuscript_sectors_sub_Btail
#print axioms manuscript_RHS_difference

end

end RHFormalization
