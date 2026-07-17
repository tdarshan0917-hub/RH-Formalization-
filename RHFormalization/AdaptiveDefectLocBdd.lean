-- SENTINEL: L3b-adaptive-defect-loc-bdd-v2
import RHFormalization.ResolventDenomCompactLowerBound
import RHFormalization.AdaptiveStageBoundUniform
import Mathlib

/-!
# L3b — THE DEFECT GATE'S LAST INPUT: loc_bdd
`adaptiveGalerkinTransformDefect_loc_bdd`: on every compact K ⊆ Ω, the
adaptive transform defects are uniformly bounded over all stages n:
  ∃ C, ∀ n, ∀ s ∈ K, ‖adaptiveGalerkinTransformDefect c n s‖ ≤ C,
with C = 5/c₀(K) + 1/c₀(K)² explicit. Chain: L0a compact floor →
L2 stage bound → L3a uniform domination. This is the sole open input to
adaptiveGalerkinTransformDefect_eps0_of_loc_bdd (the Montel/eps0 adapter).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- **loc_bdd — the defect gate closes.** -/
theorem adaptiveGalerkinTransformDefect_loc_bdd (c : ℝ) (K : Set ℂ)
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖adaptiveGalerkinTransformDefect c n s‖ ≤ C := by
  obtain ⟨c₀, hc₀, hfl⟩ := resolventDenom_lower_bound K hK hKΩ
  refine ⟨5 / c₀ + 1 / c₀^2, ?_⟩
  intro n s hs
  exact (adaptiveDefect_norm_le_stageBound c n s (hKΩ hs) c₀ hc₀
    (fun ξ => hfl s hs ξ)).trans (stageBound_uniform c n c₀ hc₀)

#print axioms adaptiveGalerkinTransformDefect_loc_bdd

end

end RHFormalization
