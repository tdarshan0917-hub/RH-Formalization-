import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import RHFormalization.OmegaMeromorphicLocalPropagationEndpoint

open Complex Topology Filter

#print RHFormalization.OmegaMeromorphicLocalPropagationAPI

-- Meromorphic algebra and local zero tools.
#check MeromorphicOn.sub
#check MeromorphicAt.sub
#check MeromorphicAt.frequently_zero_iff_eventuallyEq_zero
#check meromorphicAt_of_meromorphicOrderAt_ne_zero

-- Codiscrete analyticity / meromorphic sets.
#check MeromorphicOn.analyticAt_mem_codiscreteWithin
#check MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin
#check MeromorphicOn.eventually_analyticAt_or_mem_compl
#check MeromorphicOn.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top
#check codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top

-- Identity theorem candidates.
#check AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
#check AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
#check AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero

-- Known codiscrete/punctured conversion.
#check MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
#check mem_codiscreteWithin_iff_forall_mem_nhdsNE
#check Filter.codiscreteWithin
#check Filter.self_mem_codiscreteWithin
#check Filter.EventuallyEq.filter_mono
#check Filter.EventuallyEq.trans
#check Filter.EventuallyEq.symm

-- Omega facts.
#check RHFormalization.isPreconnected_Omega_native
#check RHFormalization.preperfect_Omega_native
#check RHFormalization.isOpen_Omega_native
