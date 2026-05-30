import Mathlib
import RHFormalization.PrincipalPartCoboundedModel

open Complex Topology Filter

variable (h : ℂ → ℂ)
variable (s0 coeff : ℂ)

#check Bornology.cobounded
#check tendsto_cobounded_of_meromorphicOrderAt_neg
#check tendsto_cobounded_iff_meromorphicOrderAt_neg

#check tendsto_add_const_cobounded
#check tendsto_const_add_cobounded
#check tendsto_sub_const_cobounded
#check tendsto_const_sub_cobounded
#check tendsto_neg_cobounded

#check Filter.Tendsto.add
#check Filter.Tendsto.sub
#check Filter.Tendsto.congr'
#check Filter.Tendsto.comp
#check Filter.Tendsto.mono_left
#check Filter.Tendsto.mono_right

#check AnalyticAt.continuousAt
#check ContinuousAt.tendsto
#check AnalyticAt.meromorphicAt
#check tendsto_nhds_of_meromorphicOrderAt_nonneg

#check meromorphicOrderAt_congr
#check meromorphicOrderAt_div
#check meromorphicOrderAt_inv
#check meromorphicOrderAt_add
#check meromorphicOrderAt_mul
#check meromorphicOrderAt_neg
#check AnalyticAt.meromorphicOrderAt_nonneg

#check analyticAt_const
#check analyticAt_id
#check AnalyticAt.sub
#check AnalyticAt.div
#check AnalyticAt.add

-- model functions
#check fun w : ℂ => coeff / (w - s0)
#check fun w : ℂ => coeff / (w - s0) + h w
#check fun w : ℂ => w - s0
#check fun w : ℂ => (w - s0)⁻¹
