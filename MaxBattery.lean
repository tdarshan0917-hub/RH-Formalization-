import RHFormalization.SphereUniformConvergence
open Complex Set Topology Filter Metric RHFormalization
-- A: ball geometry for the maximum principle
#check @Metric.isBounded_ball
#check @frontier_ball
#check @closure_ball
#check @Metric.ball_subset_closedBall
-- B: convergence -> uniform Cauchy, and back with completeness
#check @TendstoUniformlyOn.uniformCauchySeqOn
#check @UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
#check @uniformCauchySeqOn_iff
#check @cauchySeq_tendsto_of_complete
#check @cauchy_iff_exists_le_nhds
-- C: does uniform-Cauchy + complete codomain give a limit outright?
#check @UniformCauchySeqOn.exists_tendstoUniformlyOn
#check @UniformCauchySeqOn.tendstoUniformlyOn
-- D: DiffContOnCl from DifferentiableOn on a superset
example (f : ℂ → ℂ) (c : ℂ) (r1 r2 : ℝ) (h12 : 0 < r1) (h2 : r1 < r2)
    (hf : DifferentiableOn ℂ f (Metric.ball c r2)) :
    DiffContOnCl ℂ f (Metric.ball c r1) := by
  refine DifferentiableOn.diffContOnCl (hf.mono ?_)
  refine (closure_ball c (by linarith : r1 ≠ 0)).le.trans ?_
  first
    | exact Metric.closedBall_subset_ball h2
    | sorry
-- E: pointwise Cauchy at a point from UniformCauchySeqOn (for the s0 limit)
#check @UniformCauchySeqOn.cauchySeq
