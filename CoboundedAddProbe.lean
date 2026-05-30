import Mathlib
import RHFormalization.PrincipalPartCoboundedSplit

open Complex Topology Filter

variable (f g : ℂ → ℂ)
variable (l : Filter ℂ)
variable (c : ℂ)

#check Bornology.cobounded
#check Bornology.IsBounded
#check Bornology.isBounded_def
#check isBounded_def
#check Metric.isBounded_iff
#check Filter.isBounded_iff

#check tendsto_add_const_cobounded
#check tendsto_const_add_cobounded
#check tendsto_sub_const_cobounded
#check tendsto_const_sub_cobounded

#check Filter.Tendsto.add
#check Filter.Tendsto.congr'
#check Filter.Tendsto.mono_left
#check Filter.Tendsto.mono_right

#check Tendsto.isBoundedUnder
#check Filter.Tendsto.isBoundedUnder
#check isBoundedUnder_le
#check IsBoundedUnder
#check IsCoboundedUnder
#check IsBoundedUnder.mono

#check Metric.eventually_nhds_iff
#check Metric.mem_nhds_iff
#check eventually_nhds_iff
#check mem_nhds_iff
