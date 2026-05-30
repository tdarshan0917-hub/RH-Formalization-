import Mathlib
import RHFormalization.PrincipalPartMeromorphic

open Complex Topology Filter

variable (f h : ℂ → ℂ)
variable (z coeff : ℂ)

#check Bornology.cobounded
#check Tendsto
#check Filter.Tendsto.add
#check Filter.Tendsto.sub
#check Filter.Tendsto.mul
#check Filter.Tendsto.div
#check Filter.Tendsto.inv₀
#check tendsto_const_nhds
#check tendsto_id
#check nhdsWithin_le_nhds
#check self_mem_nhdsWithin

#check tendsto_cobounded_iff_meromorphicOrderAt_neg
#check tendsto_cobounded_of_meromorphicOrderAt_neg
#check tendsto_nhds_iff_meromorphicOrderAt_nonneg
#check tendsto_nhds_of_meromorphicOrderAt_nonneg

#check Tendsto.norm
#check tendsto_norm_atTop
#check tendsto_norm_cobounded
#check tendsto_cobounded_iff_norm_tendsto_atTop
#check Bornology.isBounded_iff
#check Metric.isBounded_iff
#check isBounded_iff
