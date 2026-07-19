import RHFormalization.DBFFDecodedProfiles

/-!
# DBFFProfileCompactBounds — P2-2a: profiles bounded on Ω-compacts

ROUTE CARD
1. Target: `sup_{s∈K} |Φ_j(s)| < ∞` for the banked J_free profile shapes —
   the profile half of the D.BFF.4 assembly inequality.
2. Consumer: P2-5 (D.BFF.4 assembly). 3. Raw B on Ω? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- The J_free compensator shape is bounded on every Ω-compact. -/
theorem bulkProfileFreeM_compact_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ‖bulkProfileFreeM s‖ ≤ C := by
  have hcont : ContinuousOn bulkProfileFreeM K := by
    intro z hz
    exact ((bulkProfileFreeM_analyticAt (hKO hz)).continuousAt).continuousWithinAt
  have hb := hK.exists_bound_of_continuousOn hcont
  obtain ⟨C, hC⟩ := hb
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs
  exact le_trans (hC s hs) (le_max_left _ _)

/-- The J_free pole factor is bounded on every Ω-compact. -/
theorem bulkProfilePoleFactor_compact_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ‖bulkProfilePoleFactor s‖ ≤ C := by
  have hcont : ContinuousOn bulkProfilePoleFactor K := by
    intro z hz
    exact ((bulkProfilePoleFactor_analyticAt (hKO hz)).continuousAt).continuousWithinAt
  have hb := hK.exists_bound_of_continuousOn hcont
  obtain ⟨C, hC⟩ := hb
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs
  exact le_trans (hC s hs) (le_max_left _ _)

#print axioms bulkProfileFreeM_compact_bound
#print axioms bulkProfilePoleFactor_compact_bound

end

end RHFormalization
