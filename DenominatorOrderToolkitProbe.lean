import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.SimplePoleOrderFromDenominator

open Complex Topology Filter Bornology

variable (s0 : ℂ)

#check analyticOrderAt
#check analyticOrderAt_id
#check AnalyticAt.meromorphicOrderAt_eq
#check analyticAt_id
#check analyticAt_const
#check AnalyticAt.sub
#check HasDerivAt
#check hasDerivAt_id
#check HasDerivAt.sub_const
#check HasDerivAt.sub

-- Possible order/congruence/translation lemmas
#check analyticOrderAt_congr
#check analyticOrderAt_congr'
#check analyticOrderAt_comp
#check analyticOrderAt_comp_linearEquiv
#check analyticOrderAt_comp_sub
#check analyticOrderAt_comp_add
#check analyticOrderAt_sub_const
#check analyticOrderAt_add_const
#check analyticOrderAt_eq_nat_iff
#check analyticOrderAt_eq_top_iff
#check analyticOrderAt_eq_zero_iff

-- Possible derivative-to-order lemmas
#check analyticOrderAt_eq_one_iff
#check analyticOrderAt_eq_one_of_hasDerivAt_ne_zero
#check analyticOrderAt_eq_nat_of_hasDerivAt
#check HasDerivAt.analyticOrderAt_eq_one

-- Power series route
#check HasFPowerSeriesAt
#check HasFPowerSeriesAt.order
#check FormalMultilinearSeries.order
#check PowerSeries.X
#check PowerSeries.monomial
#check hasFPowerSeriesAt_id
#check HasFPowerSeriesAt.sub
#check HasFPowerSeriesAt.sub_const
#check HasFPowerSeriesAt.const_sub

-- Target expression
#check fun w : ℂ => w - s0
