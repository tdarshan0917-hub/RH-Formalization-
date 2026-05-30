import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.OmegaNormalFormPropagationEndpoint

open Complex Topology Filter

variable (f : ℂ → ℂ)
variable (U : Set ℂ)
variable (z : ℂ)

#check MeromorphicNFAt
#print MeromorphicNFAt

#check MeromorphicNFOn
#print MeromorphicNFOn

#check toMeromorphicNFAt_eq_self
#check toMeromorphicNFOn_eq_toMeromorphicNFAt
#check toMeromorphicNFOn_eqOn_codiscrete
#check MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin
#check MeromorphicOn.analyticAt_mem_codiscreteWithin

#check MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff
#check MeromorphicNFAt.meromorphicOrderAt_eq_zero
#check MeromorphicNFAt.meromorphicAt
#check MeromorphicNFAt.analyticAt
#check MeromorphicNFAt.order_eq_zero

#check MeromorphicAt.meromorphicOrderAt_eq_zero_iff
#check meromorphicOrderAt_eq_zero_iff
