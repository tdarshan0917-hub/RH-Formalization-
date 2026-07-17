-- SENTINEL: decoded-combined-endpoint-v1
import RHFormalization.DecodedAdaptivePrimeSplit
import RHFormalization.CompensatedBDecisiveEndpoint
import Mathlib

/-!
# DECODED COMBINED ENDPOINT — RH from the two decoded sector bounds
Chain (all banked): decodedCombined = CompensatedB − decodedPrimeStage
(identity), decodedPrimeStage = decodedShort (split, on Ω), so
CompensatedB = decodedCombined + decodedShort ⟹ bounds on the two decoded
objects give the compensated-B bound ⟹ RiemannHypothesis.
The decoded frontier, frozen: hComb (combined sector estimate — the
manuscript's local/displacement/tail/bulk decomposition target) and hShort
(decoded FOW + O2 bounds — the mixed/higher-order providers).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- **RH from the decoded combined + short sector bounds.** -/
theorem RH_from_decoded_combined_and_short (c : ℝ)
    (hComb : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C1 : ℝ, ∀ n, ∀ s ∈ K, ‖decodedAdaptiveCombinedFreeR c n s‖ ≤ C1)
    (hShort : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C2 : ℝ, ∀ n, ∀ s ∈ K, ‖decodedAdaptiveShortResidual c n s‖ ≤ C2) :
    RiemannHypothesis := by
  apply RH_from_compensatedB_locbdd
  intro K hK hKΩ
  obtain ⟨C1, h1⟩ := hComb K hK hKΩ
  obtain ⟨C2, h2⟩ := hShort K hK hKΩ
  refine ⟨C1 + C2, fun n s hs => ?_⟩
  have hmem : s ∈ Ω := hKΩ hs
  have hid : compensatedBFamily n s
      = decodedAdaptiveCombinedFreeR c n s
        + decodedAdaptiveShortResidual c n s := by
    have hEq := decodedAdaptiveCombinedFreeR_eq c n s
    have hSplit := decodedFadmPrimeStage_eq_first_plus_second c n hmem
    have hCB : DBFFO3CompensatedB n s = compensatedBFamily n s := by
      first
        | rfl
        | (unfold DBFFO3CompensatedB compensatedBFamily; rfl)
    rw [← hCB]
    have hShortEq : decodedAdaptiveShortResidual c n s
        = decodedFadmPrimeStage c n s := by
      unfold decodedAdaptiveShortResidual
      rw [← hSplit]
    rw [hShortEq]
    first
      | linear_combination hEq
      | linear_combination -hEq
      | (rw [hEq]; ring)
      | (have h := hEq; linear_combination h)
  rw [hid]
  calc ‖decodedAdaptiveCombinedFreeR c n s
        + decodedAdaptiveShortResidual c n s‖
      ≤ ‖decodedAdaptiveCombinedFreeR c n s‖
        + ‖decodedAdaptiveShortResidual c n s‖ := norm_add_le _ _
    _ ≤ C1 + C2 := add_le_add (h1 n s hs) (h2 n s hs)

#print axioms RH_from_decoded_combined_and_short

end

end RHFormalization
