import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import RHFormalization.DefaultSimplePoleCoboundedFromOrder

open Complex Topology Filter Bornology

variable (s0 coeff : ℂ)
variable (hcoeff : coeff ≠ 0)

#check meromorphicOrderAt
#check analyticOrderAt
#check AnalyticAt.meromorphicOrderAt_eq
#check AnalyticAt.meromorphicOrderAt_nonneg

-- Constant / nonzero constant order possibilities
#check meromorphicOrderAt_const
#check meromorphicOrderAt_const_of_ne
#check meromorphicOrderAt_const_ne_zero
#check analyticOrderAt_const
#check analyticOrderAt_const_of_ne
#check analyticAt_const

-- Identity / affine linear order possibilities
#check analyticOrderAt_id
#check analyticOrderAt_sub_const
#check analyticOrderAt_sub
#check analyticOrderAt_of_hasDerivAt_ne_zero
#check analyticOrderAt_eq_nat_iff
#check analyticOrderAt_eq_zero_iff
#check analyticOrderAt_eq_top_iff
#check hasDerivAt_id
#check HasDerivAt.sub_const
#check hasDerivAt_const
#check HasDerivAt.sub

-- Meromorphic quotient order
#check meromorphicOrderAt_div
#check meromorphicOrderAt_inv
#check MeromorphicAt.div
#check AnalyticAt.meromorphicAt

-- Arithmetic/order on WithTop ℤ
#check WithTop.coe_lt_coe
#check WithTop.coe_zero
#check WithTop.coe_neg
#check sub_eq_add_neg
#check Int.negSucc_lt_zero
#check show ((-1 : ℤ) : WithTop ℤ) < 0 from by norm_num
