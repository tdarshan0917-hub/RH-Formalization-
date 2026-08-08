import RHFormalization.ObstructionHalfplaneBound
import RHFormalization.DMROmegaCoreMontel
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-!
# CanonicalRcanLocBddReduction — the frozen target and its two cases

FROZEN TARGET: canonicalRcanStage loc-bdd on Ω-compacts.
(1) Ω-REDUCTION: it follows from obstruction loc-bdd alone (core banked).
(2) HALF-PLANE CASE: unconditional, from today's obstruction bound.
The sole remaining open input: the obstruction bound on Ω-compacts near
the cut. No other slot.
-/

/-- **The reduction**: the frozen target follows from the obstruction bound;
everything else is banked. -/
theorem canonicalRcanStage_locbdd_of_obstruction
    (hOB : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖canonicalRcanStage n s - galOmegaCore n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖canonicalRcanStage n s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨C1, h1⟩ := galOmegaCore_loc_bdd K hK hKΩ
  obtain ⟨C2, h2⟩ := hOB K hK hKΩ
  refine ⟨C1 + C2, fun n s hs => ?_⟩
  calc ‖canonicalRcanStage n s‖
      = ‖galOmegaCore n s + (canonicalRcanStage n s - galOmegaCore n s)‖ := by
        congr 1; ring
    _ ≤ ‖galOmegaCore n s‖ + ‖canonicalRcanStage n s - galOmegaCore n s‖ :=
        norm_add_le _ _
    _ ≤ C1 + C2 := add_le_add (h1 n s hs) (h2 n s hs)

/-- **The half-plane case, unconditional**: on compacts within `Re s ≥ σ > 0`
the frozen target holds. -/
theorem canonicalRcanStage_locbdd_on_halfplane
    (σ : ℝ) (hσ : 0 < σ) (K : Set ℂ) (hK : IsCompact K)
    (hKσ : ∀ s ∈ K, σ ≤ s.re) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖canonicalRcanStage n s‖ ≤ C := by
  have hKΩ : K ⊆ Ω := halfplane_subset_Omega σ hσ K hKσ
  obtain ⟨C1, h1⟩ := galOmegaCore_loc_bdd K hK hKΩ
  obtain ⟨C2, h2⟩ := canonicalTailObstruction_uniform_bound_on_halfplane
    σ hσ K hK hKσ
  refine ⟨C1 + C2, fun n s hs => ?_⟩
  have hsre : 0 < s.re := lt_of_lt_of_le hσ (hKσ s hs)
  have hsplit := canonicalRcanStage_eq_head_add_Ftail_add_obstruction n s hsre
  calc ‖canonicalRcanStage n s‖
      = ‖galOmegaCore n s + canonicalTailObstruction n s‖ := by
        rw [hsplit]
        unfold galOmegaCore
        first
          | rfl
          | (congr 1; ring)
          | ring_nf
    _ ≤ ‖galOmegaCore n s‖ + ‖canonicalTailObstruction n s‖ := norm_add_le _ _
    _ ≤ C1 + C2 := add_le_add (h1 n s hs) (h2 n s hs)

#print axioms canonicalRcanStage_locbdd_of_obstruction
#print axioms canonicalRcanStage_locbdd_on_halfplane

end

end RHFormalization
