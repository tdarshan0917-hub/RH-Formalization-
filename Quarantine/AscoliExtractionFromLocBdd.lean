import RHFormalization.AscoliObligationDirect
import RHFormalization.AscoliBridgeLayer3
import RHFormalization.MontelEquicontinuousOn
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Filter Topology Complex Metric Set

/-
Goal:
  h_stage_holo + h_loc_bdd
  → AscoliExtractionHyp F.

This is the missing bridge. It should use:
  ascoliRelCompactObligation_direct
  ascoliRelativelyCompact_of_obligation
  uniformEquicontinuousOn_ball_of_bounded_holo

If this first attempt errors, the error should name the exact shape mismatch.
-/
theorem ascoliExtractionHyp_of_holo_loc_bdd
    (F : ℕ → ℂ → ℂ)
    (h_loc_bdd :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) :
    AscoliExtractionHyp F := by
  intro hF
  -- Need:
  -- AscoliRelativelyCompact (fun n => bundleC (F n) (hF n))
  apply ascoliRelativelyCompact_of_obligation
    ascoliRelCompactObligation_direct
  · intro x n
    -- pointwise bound at x from compact singleton {x}
    obtain ⟨C, hC⟩ := h_loc_bdd ({(x : ℂ)} : Set ℂ) isCompact_singleton ?_
    · have hx : (x : ℂ) ∈ ({(x : ℂ)} : Set ℂ) := by simp
      have hb := hC n (x : ℂ) hx
      -- Need membership in closedBall 0 (some M x). choose M x = C.
      -- If C may be negative, use |C| + 1.
      sorry
    · intro z hz
      simpa using x.property
  ·
    -- equicontinuity from local boundedness + holomorphicity
    sorry

#print axioms ascoliExtractionHyp_of_holo_loc_bdd

end
end RHFormalization
