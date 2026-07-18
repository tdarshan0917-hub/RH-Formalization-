import RHFormalization.HMeromorphicPackage
open Complex Set
#check @riemannZeta
#check @differentiableAt_riemannZeta
#check @riemannZeta_one_ne_zero
#check @AnalyticAt.eventually_eq_zero_or_eventually_ne_zero
#check @AnalyticOnNhd.isPreconnected_setOf_eq_zero
#check fun (f : ℂ → ℂ) (U : Set ℂ) (h : AnalyticOnNhd ℂ f U) => h
#check @Set.Countable.exists_eq_range
#check @Set.Finite.subset
#check @Polynomial.setOf_isRoot_finite
#check @TopologicalSpace.SeparableSpace
#check @Set.Countable.mono
example : (∅ : Set ℂ).Countable := Set.countable_empty
