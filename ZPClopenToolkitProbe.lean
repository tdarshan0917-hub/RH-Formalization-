import RHFormalization.OmegaMeromorphicZeroPropagationProof
import Mathlib.Topology.Connected.Basic

open Complex Topology Filter

variable (S U : Set ℂ)

#check IsPreconnected
#check RHFormalization.isPreconnected_Omega_native

-- Clopen / separation tools
#check IsPreconnected.subset
#check IsPreconnected.subset_closure
#check IsPreconnected.isClopen
#check IsPreconnected.eq_univ_of_isClosed_isOpen
#check IsPreconnected.eq_of_isOpen_isClosed
#check IsPreconnected.union
#check isPreconnected_iff_connectedSpace

-- Open/closed set basics
#check IsOpen
#check IsClosed
#check isOpen_compl_iff
#check isClosed_compl_iff
#check IsOpen.mem_nhds
#check eventually_nhds_iff
#check eventually_nhdsWithin_iff
#check nhdsWithin_le_nhds
#check Filter.EventuallyEq.filter_mono
#check mem_closure_iff_clusterPt
#check Set.EqOn
