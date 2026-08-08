import RHFormalization.ObstructionPairedForm
import RHFormalization.CanonicalRcanLocBddReduction
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-!
# FourSectorAccounting — manuscript D.UNIFORM-CAN-BOUND vs the machine

Manuscript sectors, filled with banked objects:
  Rshort+win := galHead + BcorrWin + shortDensityGap   (t ≤ t₀ objects)
  Rtail      := galFTailClosed                         (spectral, Step 3)
  Rbulk      := compensatorPole                        (finite transform, Step 4)
Machine adjudication: the exact residual after all four sectors.
Manuscript Thm 5.2 restricts the spike decomposition to 0 < t ≤ t₀;
no sector is defined to contain the large-time spike tail.
-/

/-- The manuscript's short+window sector, in banked coordinates. -/
noncomputable def sectorShortWin (n : ℕ) (s : ℂ) : ℂ :=
  galHead n s + BcorrWin n s + shortDensityGap n s

/-- **FOUR-SECTOR ACCOUNTING (exact, Re s > 0)**: after filling every
manuscript sector, the residual is exactly `pairedTailGap`. -/
theorem fourSector_accounting (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    canonicalRcanStage n s
      = sectorShortWin n s
        + galFTailClosed n s
        + compensatorPole s
        + pairedTailGap n s := by
  rw [canonicalRcanStage_eq_head_add_Ftail_add_obstruction n s hs,
    obstruction_eq_paired_form n s hs]
  unfold sectorShortWin
  ring

#print axioms sectorShortWin
#print axioms fourSector_accounting

end

end RHFormalization
