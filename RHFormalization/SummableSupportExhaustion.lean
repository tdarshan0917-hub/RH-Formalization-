import Mathlib

/-!
# Partial sums over support-covering finsets converge to the tsum

If `f : ι → ℂ` is summable and `A : ℕ → Finset ι` eventually covers the support
(every `i` with `f i ≠ 0` is eventually in `A n`), then `∑_{i ∈ A n} f i → ∑' i, f i`.

Proof: ε-S. `HasSum` gives a finite `S₀` with `‖∑_T f − tsum‖ < ε` for all `T ⊇ S₀`.
The support elements of `S₀` are eventually in `A n` (finite conjunction of the cover
hypothesis). For such `n`, `∑_{A n} f = ∑_{A n ∪ S₀} f` (the difference `S₀ ∖ A n` lies
off the support, so `f = 0` there), and `A n ∪ S₀ ⊇ S₀`, giving the bound.
-/

namespace RHFormalization

open Filter Topology

theorem tendsto_sum_of_eventually_covers_support
    {ι : Type*} [DecidableEq ι] {f : ι → ℂ}
    (hf : Summable f)
    {A : ℕ → Finset ι}
    (hcover : ∀ i, f i ≠ 0 → ∀ᶠ n in atTop, i ∈ A n) :
    Tendsto (fun n => ∑ i ∈ A n, f i) atTop (𝓝 (∑' i, f i)) := by
  have hHS : HasSum f (∑' i, f i) := hf.hasSum
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- HasSum unpacked: ∃ S₀, ∀ T ⊇ S₀, dist (∑_T f) tsum < ε
  obtain ⟨S₀, hS₀⟩ := (Metric.tendsto_atTop.mp hHS) ε hε
  -- The support-points inside S₀ are each eventually in A n; S₀ is finite.
  have hcov : ∀ᶠ n in atTop, ∀ i ∈ S₀, f i ≠ 0 → i ∈ A n := by
    have hper : ∀ i ∈ S₀, ∀ᶠ n in atTop, f i ≠ 0 → i ∈ A n := by
      intro i _
      by_cases hfi : f i = 0
      · refine Eventually.of_forall (fun n => ?_)
        intro hne
        exact absurd hfi hne
      · filter_upwards [hcover i hfi] with n hn
        intro _
        exact hn
    exact (Filter.eventually_all_finite S₀.finite_toSet).2 (by simpa using hper)
  -- The goal is `∃ N, ∀ n ≥ N, dist (∑_{A n} f) tsum < ε`.
  -- Convert hcov (a `∀ᶠ`) to that form via eventually_atTop.
  rw [← Filter.eventually_atTop]
  filter_upwards [hcov] with n hn
  -- Show ∑_{A n} f = ∑_{A n ∪ S₀} f, then use hS₀ on (A n ∪ S₀) ⊇ S₀.
  have hsub : A n ⊆ A n ∪ S₀ := Finset.subset_union_left
  have hpad : ∑ i ∈ A n, f i = ∑ i ∈ A n ∪ S₀, f i := by
    apply Finset.sum_subset hsub
    intro i hi hni
    by_contra hfne
    have hiS₀ : i ∈ S₀ := by
      rcases Finset.mem_union.mp hi with h | h
      · exact absurd h hni
      · exact h
    exact hni (hn i hiS₀ hfne)
  rw [hpad]
  exact hS₀ (A n ∪ S₀) Finset.subset_union_right

end RHFormalization
