import Mathlib
import RHFormalization.PrincipalPartCoboundedSplit

open Complex Topology Filter

variable (s t : Set ℂ)
variable (f g : ℂ → ℂ)
variable (l : Filter ℂ)
variable (c : ℂ)

#check Bornology.IsBounded
#check Bornology.isBounded_def
#check Metric.isBounded_iff

#check Bornology.IsBounded.image
#check Bornology.IsBounded.add
#check Bornology.IsBounded.sub
#check Bornology.IsBounded.union
#check Bornology.IsBounded.singleton
#check Bornology.IsBounded.insert

#check isBounded_range
#check isBounded_range_iff
#check isBounded_iff_eventually_norm_le
#check bounded_range_iff

#check Filter.Tendsto.eventually
#check Filter.Tendsto.mem
#check tendsto_add_const_cobounded
#check tendsto_const_add_cobounded
