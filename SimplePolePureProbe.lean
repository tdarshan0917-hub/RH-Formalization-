import Mathlib
import RHFormalization.DefaultCoboundedAddFiniteLimit

open Complex Topology Filter Bornology

variable (s0 coeff : ℂ)
variable (hcoeff : coeff ≠ 0)

#check tendsto_cobounded_of_meromorphicOrderAt_neg
#check tendsto_cobounded_iff_meromorphicOrderAt_neg
#check meromorphicOrderAt_congr
#check meromorphicOrderAt_div
#check meromorphicOrderAt_inv
#check meromorphicOrderAt_mul
#check meromorphicOrderAt_add
#check AnalyticAt.meromorphicOrderAt_nonneg
#check AnalyticAt.meromorphicOrderAt_eq
#check analyticAt_const
#check analyticAt_id
#check AnalyticAt.sub
#check AnalyticAt.div
#check AnalyticAt.inv
#check AnalyticAt.meromorphicAt

#check tendsto_inv_nhds_zero
#check tendsto_inv_nhdsWithin_zero
#check tendsto_inv₀_nhdsWithin_zero
#check tendsto_cobounded_nhdsWithin_zero
#check tendsto_norm_atTop
#check tendsto_norm_cobounded
#check Bornology.isBounded_def
#check Metric.isBounded_iff

#check fun w : ℂ => coeff / (w - s0)
#check fun w : ℂ => (w - s0)
#check fun w : ℂ => (w - s0)⁻¹
