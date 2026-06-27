import RHFormalization.SelectedFiniteCanonicalLimit
import RHFormalization.PrimePowerDFiniteStage
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Selected index exhaustion.

This proves the `hmem` input needed by `buildSelectedFiniteCanonicalLimit`.

Path:
  IsPrimePowerPair q
  → eventually q.center ≤ (primePowerStage n).R
  → primePowerStage completeness gives an active Nat code k with toPP k = q
  → selectedFiniteIndices image contains q
-/
theorem selectedFiniteIndices_eventually_contains_valid :
    ∀ q : PrimePowerPair, IsPrimePowerPair q →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        q ∈ selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
              (primePowerStage n) := by
  intro q hq
  -- use R(n) → ∞ to eventually dominate q.center
  have hR := primePowerStage_R_tendsto_atTop
  rw [Filter.tendsto_atTop_atTop] at hR
  rcases hR q.center with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hcenter : q.center ≤ (primePowerStage n).R := hN n hn

  -- unfold the selected layer/payload down to selectedFiniteIndices
  change q ∈ selectedFiniteIndices (primePowerStage n)

  -- primePowerStage contains every valid prime power below cutoff
  rcases (primePowerStage n).h_diagonalSpikeToPP_complete_center_le_R q hq hcenter with
    ⟨k, hk_active, hk_eq⟩

  -- selectedFiniteIndices is the image of active Nat indices through toPP
  unfold selectedFiniteIndices
  refine Finset.mem_image.mpr ?_
  exact ⟨k, hk_active, hk_eq⟩

#print axioms selectedFiniteIndices_eventually_contains_valid

end
end RHFormalization
