import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Analytic.Basic
import RHFormalization.LocalOrderObstruction

open Complex Topology Filter

variable (s0 coeff : ℂ)
variable (hcoeff : coeff ≠ 0)

#check meromorphicOrderAt
#check meromorphicOrderAt_congr
#check meromorphicOrderAt_inv
#check meromorphicOrderAt_div
#check meromorphicOrderAt_mul
#check meromorphicOrderAt_add
#check meromorphicOrderAt_neg
#check meromorphicOrderAt_fun_neg

#check analyticAt_const
#check analyticAt_id
#check AnalyticAt.const
#check AnalyticAt.sub
#check AnalyticAt.add
#check AnalyticAt.div
#check AnalyticAt.inv
#check AnalyticAt.meromorphicAt
#check AnalyticAt.meromorphicOrderAt_nonneg

#check tendsto_cobounded_of_meromorphicOrderAt_neg
#check tendsto_cobounded_iff_meromorphicOrderAt_neg
#check tendsto_nhds_of_meromorphicOrderAt_nonneg
#check tendsto_nhds_iff_meromorphicOrderAt_nonneg

#check Tendsto.add
#check Tendsto.sub
#check Tendsto.div
#check Tendsto.inv₀
#check tendsto_const_nhds
#check tendsto_id
#check tendsto_nhdsWithin_iff
#check nhdsWithin_le_nhds

-- Test the function syntax for the simple pole.
#check fun z : ℂ => coeff / (z - s0)
#check fun z : ℂ => (z - s0)
#check fun z : ℂ => (z - s0)⁻¹
