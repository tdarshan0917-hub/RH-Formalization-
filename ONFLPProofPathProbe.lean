import RHFormalization.OmegaNormalFormLocalPropagationEndpoint
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Topology Filter

variable (f g : ℂ → ℂ)
variable (z₀ : ℂ)

#print RHFormalization.OmegaNormalFormLocalPropagationAPI

-- Can we prove the Ω-normal forms are meromorphic on Ω?
#check toMeromorphicNFOn_eqOn_codiscrete
#check MeromorphicOn.congr_codiscreteWithin_of_eqOn_compl
#check MeromorphicNFOn.meromorphicOn
#check meromorphicNFAt_toMeromorphicNFAt
#check toMeromorphicNFAt_eq_self
#check toMeromorphicNFOn_eq_toMeromorphicNFAt
#check MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin
#check MeromorphicOn.analyticAt_mem_codiscreteWithin

-- Local-to-global identity tools.
#check MeromorphicAt.frequently_zero_iff_eventuallyEq_zero
#check AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
#check AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check AnalyticAt.frequently_eq_iff_eventually_eq

-- Codiscrete conversion/filter tools.
#check Filter.codiscreteWithin
#check Filter.self_mem_codiscreteWithin
#check mem_codiscreteWithin
#check mem_codiscreteWithin_iff_forall_mem_nhdsNE
#check Filter.EventuallyEq.filter_mono
#check Filter.EventuallyEq.trans
#check Filter.EventuallyEq.symm

-- Ω facts already proved.
#check RHFormalization.isPreconnected_Omega_native
#check RHFormalization.preperfect_Omega_native
#check RHFormalization.isOpen_Omega_native
