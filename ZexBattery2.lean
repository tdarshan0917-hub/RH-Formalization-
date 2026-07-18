import RHFormalization.HMeromorphicPackage
open Complex Set Topology Filter
#check @riemannZeta_ne_zero_of_one_lt_re
#check @riemannZeta_two
#check @DifferentiableOn.analyticOnNhd
#check @DifferentiableAt.analyticAt
#check @AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
#check @AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
#check @Convex.isPreconnected
#check @IsCompact.tendsto_subseq
#check @AccPt
#check @accPt_iff_frequently
#check @Set.Infinite.exists_nat_lt
#check @Set.infinite_coe_iff
#check @Set.Finite.ofFinset
#check @Filter.Frequently.mono
#check @tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
#check @Complex.abs_im_le_abs
example : Convex ℝ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  first
    | exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
    | sorry
example : (2:ℂ).re = 2 := by norm_num
