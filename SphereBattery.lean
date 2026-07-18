import RHFormalization.HPPStabilization
open Complex Set Topology Filter Metric RHFormalization
#check @isCompact_sphere
#check @Metric.sphere_subset_closedBall
#check @TendstoLocallyUniformlyOn.tendstoUniformlyOn
#check @tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn
#check @IsCompact.tendstoLocallyUniformlyOn_iff
#check @nhds_basis_closedBall
#check @Metric.mem_sphere
#check @mem_sphere_iff_norm
example (U : Set ℂ) (hU : IsOpen U) (z : ℂ) (hz : z ∈ U) :
    ∃ ε > 0, Metric.closedBall z ε ⊆ U := by
  first
    | exact (Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)).imp
        (fun ε h => ⟨h.1, h.2⟩)
    | simpa using (Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz))
    | sorry
example (r : ℝ) (hr : 0 < r) (c : ℂ) (s : ℂ) (hs : s ∈ Metric.sphere c r) : s ≠ c := by
  intro h
  rw [Metric.mem_sphere, h, dist_self] at hs
  linarith
