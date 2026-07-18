import RHFormalization.MeromorphyAssembly
open Complex Set Topology Filter Metric RHFormalization
-- A: the Weierstrass M-test family
#check @tendstoUniformlyOn_tsum
#check @tendstoUniformlyOn_tsum_nat
#check @Summable.tendstoUniformlyOn_tsum
-- B: countability of the zero set from the exhaustion
#check @Set.countable_iUnion
#check @Set.Finite.countable
#check @Set.Countable.exists_eq_range
-- C: tsum over subtypes / reindexing
#check @tsum_subtype
#check @Equiv.tsum_eq
#check @Summable.of_norm_bounded
