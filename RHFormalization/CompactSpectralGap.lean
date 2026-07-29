-- SENTINEL: CGAP-v1
import RHFormalization.BallCutDistance
import RHFormalization.SplitRemainderZWiring
import Mathlib

/-!
# CompactSpectralGap — input 2 of 4 for the Z bound

CONSUMER: the `hδ`, `hlowF`, `hlowP` hypotheses of
`norm_split_remainder_trace_le` (ZWIRE).

For every compact K ⊆ Ω there is δ > 0 with δ ≤ ‖s + λ‖ for ALL s ∈ K and ALL
λ ≥ 0 — hence for both the free spectrum and the perturbed spectrum at once
(both nonneg). δ := min over K of the banked `psiCut`, positive by
`psiCut_pos_of_mem_Omega` and attained by compactness.

Not a hypothesis: this is the concrete uniform statement.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Metric

/-- **Input 2 of 4: uniform spectral gap on a compact subset of Ω.** -/
theorem compact_spectral_gap
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hne : K.Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ K, ∀ lam : ℝ, 0 ≤ lam → δ ≤ ‖s + (lam : ℂ)‖ := by
  obtain ⟨s0, hs0K, hs0min⟩ :=
    hK.exists_isMinOn hne (continuous_psiCut.continuousOn)
  refine ⟨psiCut s0, psiCut_pos_of_mem_Omega (hKΩ hs0K), ?_⟩
  intro s hs lam hlam
  exact le_trans (hs0min hs) (psiCut_le_norm_add s lam hlam)

/-- Uniform bound for ‖s‖ on a compact set (the `M` input of ZWIRE). -/
theorem compact_norm_bound
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ K, ‖s‖ ≤ M := by
  obtain ⟨s1, hs1K, hs1max⟩ :=
    hK.exists_isMaxOn hne (continuous_norm.continuousOn)
  refine ⟨‖s1‖, norm_nonneg _, fun s hs => hs1max hs⟩

#print axioms compact_spectral_gap
#print axioms compact_norm_bound

end

end RHFormalization
