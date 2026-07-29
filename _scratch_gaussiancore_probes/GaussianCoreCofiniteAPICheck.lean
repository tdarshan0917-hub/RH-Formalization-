import RHFormalization.CanonicalPrimePowerHeatKernelPrimePowerSupport
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianMajorant
import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

open Filter
open scoped BigOperators

#check Filter.eventually_cofinite
#check Set.Finite.eventually_cofinite
#check Set.finite_Iio
#check Set.finite_Icc
#check Set.Finite.subset
#check Set.Finite.union
#check Set.Finite.image
#check Finset.finite_toSet
#check Function.HasFiniteSupport
#check summable_of_finite_support
#check Nat.Prime.two_le
#check Nat.one_le_pow
#check Nat.pow_le_pow_left
#check Nat.pow_le_pow_right
#check Nat.lt_of_lt_of_le
#check Nat.le_of_lt_succ
#check Nat.succ_le_of_lt
#check Nat.exists_eq_succ_of_ne_zero

#check heatKernelGaussianCoreEnvelope_eq_zero_of_not_isPrimePowerPair
#check heatKernelGaussianCoreEnvelope_nonneg
#check heatKernelGaussianCoreEnvelope_le_weight_mul_natValue_inv_cube_of_ge
#check heatKernelNatValueMajorant
#check heatKernelNatValueMajorant_summable

end RHFormalization
