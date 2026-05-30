import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Analytic.IsolatedZeros
import RHFormalization.FinalConditionalSpine

open Complex Topology Filter

variable (f g : ℂ → ℂ)
variable (V : Set ℂ)
variable (z₀ : ℂ)

#check Filter.codiscreteWithin
#check Filter.self_mem_codiscreteWithin
#check mem_codiscreteWithin
#check mem_codiscreteWithin_iff_forall_mem_nhdsNE

#check IsOpen.mem_nhds
#check nhdsWithin_le_nhds
#check eventually_nhdsWithin_iff

#check AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
#check AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check AnalyticAt.frequently_eq_iff_eventually_eq

#check Filter.EventuallyEq.filter_mono
#check Filter.EventuallyEq.trans
#check Filter.EventuallyEq.symm
