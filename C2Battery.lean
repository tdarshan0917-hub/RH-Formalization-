import RHFormalization.MeromorphyAssembly
open Complex Set Topology Filter Metric RHFormalization
-- A: index-filter composition for uniform convergence (the net->sequence bridge)
#check @TendstoUniformlyOn.comp
#check @tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
#check @TendstoUniformlyOnFilter.comp
-- B: tendsto atTop on the Finset lattice along our exhaustion
#check @Filter.tendsto_atTop_atTop
#check @Filter.tendsto_finset_range
#check @Finset.le_iff_subset
example (g : ℕ → Finset ℂ)
    (hmono : Monotone g) (hexh : ∀ x : ℂ, (∃ n, x ∈ g n) ∨ True) :
    True := trivial
-- C: summability comparison + subtype sums
#check @Summable.of_nonneg_of_le
#check @Summable.mul_left
#check @tsum_subtype
#check @Finset.sum_subtype
#check @Finset.subtype
-- D: the majorant arithmetic shape
example (δ R p : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R) (hp : 2*R + 1 < p) :
    (1 + p) / (p - R) ≤ 2 := by
  rw [div_le_iff₀ (by linarith)]
  linarith
