import RHFormalization.PrimeAlignedThreeSectorDecomp
import Mathlib

/-!
# BRICK 4: uniform compact bound for the tail sector (free trace)

CONSUMER (named per Section 0 rule): the `h_tail_le` conjunct of
`ConcreteThreeSectorProviderTarget` (merged into shared anchor*factor form by
the final assembly brick).

`alignedRtail μ α s = FstageFinite μ s` is stage-independent, so the bound is
continuity of a fixed function on a compact subset of Ω.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter
open scoped BigOperators

variable {N : ℕ}

/-- The free trace is continuous on any subset of Ω (termwise, via the banked
analyticity of each resolvent term; the sum step is raw `tendsto_finset_sum`). -/
theorem FstageFinite_continuousOn_of_subset_Omega
    (μ : Fin N → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (K : Set ℂ) (hKΩ : K ⊆ Ω) :
    ContinuousOn (FstageFinite μ) K := by
  intro s hs
  have hsΩ : s ∈ Ω := hKΩ hs
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      Filter.Tendsto (fun z => (z + (μ i : ℂ))⁻¹) (nhds s)
        (nhds ((s + (μ i : ℂ))⁻¹)) :=
    fun i _ => (resolvent_term_analyticAt (μ i) (hμ i) hsΩ).continuousAt
  have hsum :
      Filter.Tendsto (fun z => ∑ i, (z + (μ i : ℂ))⁻¹) (nhds s)
        (nhds (∑ i, (s + (μ i : ℂ))⁻¹)) :=
    tendsto_finset_sum _ hterm
  have hCA : ContinuousAt (FstageFinite μ) s := by
    simpa [ContinuousAt, FstageFinite] using hsum
  exact hCA.continuousWithinAt

/-- **BRICK 4 (h_tail bound, raw form).** Uniform compact bound for the tail
sector: one constant works for every stage and every point of the compact. -/
theorem alignedRtail_compact_bound
    (μ : Fin N → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (α : DFiniteStage) (s : ℂ), s ∈ K →
          ‖alignedRtail μ α s‖ ≤ C := by
  intro K hK hKΩ
  rcases hK.exists_bound_of_continuousOn
      (FstageFinite_continuousOn_of_subset_Omega μ hμ K hKΩ) with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro α s hs
  calc ‖alignedRtail μ α s‖ = ‖FstageFinite μ s‖ := rfl
    _ ≤ C := hC s hs
    _ ≤ max C 0 := le_max_left _ _

#print axioms FstageFinite_continuousOn_of_subset_Omega
#print axioms alignedRtail_compact_bound

-- SENTINEL: BRICK4-RTAIL-v3
end
end RHFormalization
