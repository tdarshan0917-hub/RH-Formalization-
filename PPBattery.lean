import RHFormalization.DefaultZeroMultiplicity
open Complex Set Topology Filter Metric
-- group 1: uniform limits of holomorphic functions
#check @TendstoLocallyUniformlyOn.analyticOnNhd
#check @TendstoLocallyUniformlyOn.differentiableOn
#check @TendstoLocallyUniformlyOn.mono
#check @TendstoLocallyUniformlyOn.congr
#check @tendstoLocallyUniformlyOn_iff_forall_isCompact
-- group 2: pole-point geometry
#check @polePoint
#check @Continuous.add
#check @isCompact_closedBall
#check @Metric.mem_closedBall
#check @Metric.sphere_subset_closedBall
#check @Metric.closedBall_subset_closedBall
-- group 3: series regrouping
#check @Finset.sum_filter_add_sum_filter_not
#check @Finset.sum_congr
#check @tendsto_sub_nhds_zero_iff
#check @Filter.Tendsto.sub
#check @Filter.Tendsto.congr'
-- group 4: witness topology + holomorphy of summands
#check @DifferentiableAt.div
#check @differentiableAt_const
#check @DifferentiableOn.analyticOnNhd
#check @AnalyticAt.sub
#check @AnalyticAt.add
example (a b : ℂ) (h : b ≠ 0) : DifferentiableAt ℂ (fun s : ℂ => a / (s + b)) (1 : ℂ) ∨ True := Or.inr trivial
-- the key upgrade lemma shape: does Mathlib have uniform-on-sphere → uniform-on-ball for holomorphic?
#check @Complex.eqOn_of_eqOn_frontier
#check @Complex.norm_le_of_forall_mem_frontier_norm_le
#check @DiffContOnCl
#check @DiffContOnCl.norm_le_of_forall_mem_frontier_norm_le
