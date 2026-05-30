import RHFormalization.FinalConditionalSpine
import RHFormalization.OmegaNormalFormPropagationEndpoint
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Topology Filter

variable (f g : ℂ → ℂ)
variable (V : Set ℂ)

-- Current remaining theorem.
#print RHFormalization.OmegaNormalFormCodiscretePropagationAPI

-- Can we show normal forms are meromorphic / normal-form everywhere?
#check MeromorphicNFAt
#check MeromorphicNFOn
#check MeromorphicNFAt.meromorphicAt
#check MeromorphicNFOn.meromorphicOn
#check meromorphicNFAt_toMeromorphicNFAt
#check toMeromorphicNFAt_eq_self
#check toMeromorphicNFOn_eq_toMeromorphicNFAt

-- Can we subtract normal forms?
#check MeromorphicAt.sub
#check MeromorphicOn.sub
#check MeromorphicAt.add
#check MeromorphicOn.add

-- Meromorphic zero/identity local tools.
#check MeromorphicAt.frequently_zero_iff_eventuallyEq_zero
#check MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect

-- Analytic identity theorem tools.
#check AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
#check AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
#check AnalyticAt.frequently_eq_iff_eventually_eq

-- Codiscrete/filter tools.
#check Filter.codiscreteWithin
#check Filter.codiscreteWithin_mono
#check Filter.self_mem_codiscreteWithin
#check mem_codiscreteWithin
#check Filter.EventuallyEq.filter_mono
#check Filter.EventuallyEq.trans
#check Filter.EventuallyEq.symm

-- Existing Omega topology facts.
#check RHFormalization.isPreconnected_Omega_native
#check RHFormalization.preperfect_Omega_native
#check RHFormalization.isOpen_Omega_native
