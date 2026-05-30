import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Analytic.IsolatedZeros
import RHFormalization.OmegaNormalFormPropagationEndpoint

open Complex Topology Filter

variable (f g : ℂ → ℂ)
variable (V : Set ℂ)

#check MeromorphicNFOn
#check MeromorphicNFAt
#check toMeromorphicNFOn
#check toMeromorphicNFAt

-- Normal-form analytic regularity candidates
#check MeromorphicNFOn.analyticOnNhd
#check MeromorphicNFOn.analyticOn
#check MeromorphicNFAt.analyticAt
#check toMeromorphicNFOn_eq_toMeromorphicNFAt
#check toMeromorphicNFAt_eq_self

-- Existing meromorphic normal-form codiscrete tools
#check toMeromorphicNFOn_eqOn_codiscrete
#check MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
#check MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin
#check MeromorphicOn.analyticAt_mem_codiscreteWithin

-- Analytic identity theorem candidates
#check AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
#check AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
#check AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
#check AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero

-- Topology already built for Ω
#check RHFormalization.isPreconnected_Omega_native
#check RHFormalization.preperfect_Omega_native
#check RHFormalization.isOpen_Omega_native

-- Filter/codiscrete tools
#check Filter.codiscreteWithin
#check Filter.codiscreteWithin_mono
#check Filter.self_mem_codiscreteWithin
#check mem_codiscreteWithin
#check Filter.EventuallyEq.filter_mono
#check Filter.EventuallyEq.trans
#check Filter.EventuallyEq.symm
