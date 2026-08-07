import RHFormalization.CanonicalRcanStage
import RHFormalization.GalerkinTailSplit
import RHFormalization.GalerkinTailHolo
import RHFormalization.GalerkinHeadIntegralBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-!
# CanonicalRcanTailReduction

Exact route alignment for the canonical corrected remainder.

No estimate is introduced here.

On RHP(0):
  canonicalRcanStage
    = galHead
      + galFTailClosed
      + canonicalTailObstruction.

The first two terms already have banked uniform compact bounds.
The final term is therefore the exact compensated large-time object that
the manuscript four-sector window/bulk mechanism must account for.

No raw B-tail bound is asserted.
-/

/-- The exact compensated tail left after extracting the banked
perturbed spectral F-tail. -/
noncomputable def canonicalTailObstruction
    (n : ℕ) (s : ℂ) : ℂ :=
  galTail n s + Bcorr n s - galFTailClosed n s

/-- Exact route alignment on the initial right half-plane. -/
theorem canonicalRcanStage_eq_head_add_Ftail_add_obstruction
    (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    canonicalRcanStage n s
      =
    galHead n s
      + galFTailClosed n s
      + canonicalTailObstruction n s := by
  unfold canonicalRcanStage canonicalTailObstruction
  rw [R_stage_eq_head_add_tail n s hs]
  ring

#print axioms canonicalTailObstruction
#print axioms canonicalRcanStage_eq_head_add_Ftail_add_obstruction

end

end RHFormalization
