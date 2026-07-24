-- SENTINEL: SEAMASM-v1
import RHFormalization.AdaptivePairedResolventSplit
import Mathlib

/-!
# PairedSeamAssembly — the seam arithmetic, kernel-locked

From the banked split `X = Y − Z` (B2: perturbed paired trace = free paired
trace − remainder):

    ‖2X − B‖ ≤ ‖2Y − B‖ + 2‖Z‖

Locks the factor of two, the sign of the remainder, and which object is
which — so the route cannot drift again. Pure normed-field algebra.

CONSUMERS: the free bridge ‖2Y − B‖ (open) and the D.LOC-1 remainder
bound ‖Z‖ (open) combine through THIS theorem to give the seam bound,
which feeds the banked h_ctail_le_of_seam_bdd.
-/

set_option autoImplicit false

namespace RHFormalization

/-- **THE SEAM ASSEMBLY**: split + triangle inequality, with the factor
of two carried explicitly. -/
theorem seam_norm_le (X Y Z B : ℂ) (h : X = Y - Z) :
    ‖2 * X - B‖ ≤ ‖2 * Y - B‖ + 2 * ‖Z‖ := by
  have hrw : 2 * X - B = (2 * Y - B) - 2 * Z := by
    rw [h]; ring
  rw [hrw]
  refine le_trans (norm_sub_le _ _) ?_
  have h2 : ‖(2:ℂ) * Z‖ = 2 * ‖Z‖ := by
    rw [norm_mul]
    norm_num
  rw [h2]

/-- Bounded free bridge + bounded remainder ⟹ bounded seam. -/
theorem seam_bdd_of_parts {X Y Z B : ℂ} {Cf Cr : ℝ}
    (h : X = Y - Z) (hf : ‖2 * Y - B‖ ≤ Cf) (hr : ‖Z‖ ≤ Cr) :
    ‖2 * X - B‖ ≤ Cf + 2 * Cr := by
  refine le_trans (seam_norm_le X Y Z B h) ?_
  have : 2 * ‖Z‖ ≤ 2 * Cr := by linarith
  linarith

#print axioms seam_norm_le
#print axioms seam_bdd_of_parts

end RHFormalization
