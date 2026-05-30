import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import RHFormalization.ConnectedOmegaMeromorphicAlgebraEndpoint

open Complex Topology Filter

#check meromorphicOrderAt
#check meromorphicOrderAt_eq_zero_iff
#check MeromorphicAt
#check MeromorphicOn
#check AnalyticAt
#check AnalyticAt.meromorphicAt
#check MeromorphicAt.order
#check MeromorphicAt.meromorphicOrderAt
#check MeromorphicAt.meromorphicOrderAt_eq_zero_iff
#check MeromorphicAt.meromorphicNFAt
#check MeromorphicNFAt
#check toMeromorphicNFAt
#check MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt
#check MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
#check MeromorphicOn.analyticAt_mem_codiscreteWithin
#check Filter.codiscreteWithin
#check nhdsWithin
