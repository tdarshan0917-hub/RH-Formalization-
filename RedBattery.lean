import RHFormalization.ReflectionPairPoleClass
open Complex Set Topology Filter Metric RHFormalization
-- A: maximum principle (frontier controls interior)
#check @Complex.norm_le_of_forall_mem_frontier_norm_le
#check @DiffContOnCl.norm_le_of_forall_mem_frontier_norm_le
#check @DiffContOnCl
#check @DifferentiableOn.diffContOnCl
-- B: uniform convergence / Cauchy machinery
#check @TendstoUniformlyOn
#check @tendstoUniformlyOn_iff
#check @UniformCauchySeqOn
#check @UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
#check @TendstoUniformlyOn.tendstoLocallyUniformlyOn
#check @tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
-- C: ball/sphere topology
#check @Metric.isCompact_sphere
#check @frontier_closedBall
#check @Metric.closedBall_mem_nhds
#check @interior_closedBall
-- D: pointwise extraction from locally uniform convergence
#check @TendstoLocallyUniformlyOn.tendsto_at
-- E: our exhaustion's eventual containment at a fixed pair
example (ρ : ℂ) (h : IsNontrivialZetaZero ρ) :
    ∃ n, ρ ∈ defaultZeroExhaustion.zeroSet n :=
  defaultZeroExhaustion.h_eventually_contains ρ h
-- F: zeroSet monotonicity? (our regions are nested — is it recorded?)
#check @zetaStripRegion
example : True := trivial
