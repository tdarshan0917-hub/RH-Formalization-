import RHFormalization.PairPoleIsolation
open Complex Set Topology Filter Metric RHFormalization
#check @Finset.sum_sdiff
#check @Finset.sdiff_union_of_subset
#check @Finset.insert_subset_iff
#check @Finset.sum_insert
#check @Finset.mem_sdiff
#check @AnalyticAt.div
#check @analyticAt_const
#check @analyticAt_id
#check @AnalyticAt.sum
#check @zeroPoleDenom
#check @zeroPoleSummand
#check @finiteZeroPoleSeries
example (ρ s : ℂ) : zeroPoleDenom ρ s = s - polePoint ρ := by
  unfold zeroPoleDenom polePoint; ring
example (W : ZeroWitness) (s : ℂ) :
    zeroPoleDenom W.ρ s = s - W.s0 := by
  rw [W.hs0_def]; unfold zeroPoleDenom polePoint; ring
example (W : ZeroWitness) :
    (∃ n, W.ρ ∈ defaultZeroExhaustion.zeroSet n) ∧
    (∃ m, (1 - W.ρ) ∈ defaultZeroExhaustion.zeroSet m) :=
  ⟨defaultZeroExhaustion.h_eventually_contains W.ρ W.h_zero,
   defaultZeroExhaustion.h_eventually_contains (1 - W.ρ)
     (reflected_zero W.ρ W.h_zero)⟩
