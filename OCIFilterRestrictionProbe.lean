import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.OmegaCodiscreteIdentityFromNormalForms

open Complex Topology Filter

variable (U V : Set ℂ)
variable (hVU : V ⊆ U)
variable (f g : ℂ → ℂ)

#check Filter.codiscreteWithin
#check Filter.self_mem_codiscreteWithin
#check mem_codiscreteWithin

-- Possible monotonicity/restriction lemmas
#check Filter.codiscreteWithin_mono
#check codiscreteWithin_mono
#check Filter.codiscreteWithin_le
#check codiscreteWithin_le
#check codiscreteWithin_inter
#check Filter.codiscreteWithin_inter

-- Eventually/equality transport
#check Filter.EventuallyEq.trans
#check Filter.EventuallyEq.symm
#check Filter.EventuallyEq.mono
#check Filter.EventuallyEq.filter_mono
#check eventually_mono

-- Normal-form equality theorem
#check toMeromorphicNFOn_eqOn_codiscrete

-- Basic filter order tools
#check Filter.inf_le_left
#check Filter.inf_le_right
#check le_inf
#check inf_le_inf
