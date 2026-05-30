import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import RHFormalization.ConnectedOmegaMeromorphicAlgebraEndpoint

open Complex Topology Filter

#check meromorphicOrderAt
#check AnalyticAt.meromorphicOrderAt_nonneg
#check AnalyticAt.meromorphicOrderAt_eq
#check tendsto_cobounded_of_meromorphicOrderAt_neg
#check tendsto_nhds_iff_meromorphicOrderAt_nonneg
#check tendsto_nhds_of_meromorphicOrderAt_nonneg
#check meromorphicAt_of_meromorphicOrderAt_ne_zero

#check meromorphicOrderAt_congr
#check meromorphicOrderAt_fun_neg
#check meromorphicOrderAt_neg
#check meromorphicOrderAt_add
#check meromorphicOrderAt_sub
#check meromorphicOrderAt_mul
#check meromorphicOrderAt_inv
#check meromorphicOrderAt_div

#check AnalyticAt.meromorphicAt
#check MeromorphicAt.add
#check MeromorphicAt.sub
#check MeromorphicAt.neg
#check MeromorphicAt.div
#check MeromorphicAt.inv
