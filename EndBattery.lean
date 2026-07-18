import RHFormalization.HPPCauchyUpgrade
open Complex Set Topology Filter Metric RHFormalization
-- A: pointwise extraction from uniform / locally-uniform convergence
#check @TendstoUniformlyOn.tendsto_at
#check @TendstoLocallyUniformlyOn.tendsto_at
-- B: index shift on atTop
#check @Filter.tendsto_add_atTop_iff_nat
#check @Filter.tendsto_add_atTop_nat
-- C: singleton compacts + ball topology
#check @isCompact_singleton
#check @Metric.ball_mem_nhds
#check @Metric.mem_ball_self
#check @Metric.isOpen_ball
-- D: limit-uniqueness + arithmetic of limits
#check @tendsto_nhds_unique
#check @Filter.Tendsto.sub_const
#check @Filter.Tendsto.sub
-- E: the analytic upgrade chain on the open ball (composite test)
example (F : ℕ → ℂ → ℂ) (h : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hconv : TendstoUniformlyOn F h Filter.atTop (Metric.closedBall c r))
    (hdiff : ∀ n, DifferentiableOn ℂ (F n) (Metric.ball c r)) :
    AnalyticAt ℂ h c := by
  have h1 : TendstoLocallyUniformlyOn F h Filter.atTop (Metric.ball c r) :=
    (hconv.tendstoLocallyUniformlyOn).mono Metric.ball_subset_closedBall
  have h2 : DifferentiableOn ℂ h (Metric.ball c r) :=
    h1.differentiableOn (Filter.Eventually.of_forall hdiff) Metric.isOpen_ball
  exact (h2.analyticOnNhd Metric.isOpen_ball) c (Metric.mem_ball_self hr)
