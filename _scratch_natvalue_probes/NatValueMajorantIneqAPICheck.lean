import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

open Complex Topology Filter
open scoped BigOperators

#check Real.log_le_self
#check Real.log_le_sub_one_of_pos
#check Real.log_nonneg
#check Real.sqrt_pos
#check Real.sq_sqrt
#check inv_le_inv_of_le₀
#check one_div_le_one_div_of_le
#check mul_le_mul
#check mul_le_mul_of_nonneg_left
#check mul_le_mul_of_nonneg_right
#check pow_le_pow_left₀
#check Nat.one_le_pow
#check Nat.Prime.two_le
#check Nat.succ_le_iff
#check Real.summable_one_div_nat_add_rpow

#print PrimePowerPair.natValue
#print PrimePowerPair.weightReal
#print PrimePowerPair.weightC
#print IsPrimePowerPair
#print heatKernelNatValueMajorant
#print heatKernelPairPSeriesModel

end RHFormalization
