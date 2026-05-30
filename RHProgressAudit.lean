import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDSpikeSumExtraction
import RHFormalization.AppendixDOperatorFiniteCanonicalDetailedConstruction
import RHFormalization.CanonicalPrimePowerExhaustion
import RHFormalization.CanonicalPrimePowerSeries
import RHFormalization.CanonicalPrimePowerKernelSeries
import RHFormalization.CanonicalPrimePowerIndexExhaustion
import RHFormalization.CanonicalPrimePowerTsumSeries
import RHFormalization.CanonicalPrimePowerConcreteTsumPackage
import RHFormalization.CanonicalPrimePowerSummabilityMajorant
import RHFormalization.CanonicalPrimePowerAsymptoticKernel
import RHFormalization.CanonicalPrimePowerKernelErrorBound
import RHFormalization.CanonicalPrimePowerFiniteKernelErrorSum
import RHFormalization.CanonicalPrimePowerSummedKernelError
import RHFormalization.CanonicalPrimePowerActualKernelError
import RHFormalization.CanonicalPrimePowerWindowMassError
import RHFormalization.CanonicalPrimePowerUniformWindowError
import RHFormalization.CanonicalPrimePowerSharedKernelMajorant
import RHFormalization.CanonicalPrimePowerProductWindowError
import RHFormalization.CanonicalPrimePowerMassGrowthWindow
import RHFormalization.AppendixESharedPackageFunctionalCompatibility
import RHFormalization.OmegaMeromorphicZeroPropagationClopen

/-!
# RH formalization progress audit

This file is only an audit dashboard.

It checks the current compiled spine:
F-side zero propagation,
E-side shared-package compatibility,
D-side finite spike extraction,
and the D-side canonical prime-power finite-to-limit reduction chain.
-/

-- ============================================================
-- F-side / global spine endpoints
-- ============================================================

#check RHFormalization.finalRHSpine_after_zeroPropagation
#check RHFormalization.finalRHSpine_after_sharedPackageFunctionalCompatibility

#print axioms RHFormalization.finalRHSpine_after_zeroPropagation
#print axioms RHFormalization.finalRHSpine_after_sharedPackageFunctionalCompatibility

-- ============================================================
-- D-side finite spike extraction
-- ============================================================

#check RHFormalization.DFiniteStagePackageFromOperatorLayer.spikeSumData
#check RHFormalization.DFiniteStagePackageFromOperatorLayer.toFiniteCanonicalPrimePowerFormula
#check RHFormalization.buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums

#print axioms RHFormalization.DFiniteStagePackageFromOperatorLayer.toFiniteCanonicalPrimePowerFormula
#print axioms RHFormalization.buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums

-- ============================================================
-- D-side detailed construction from finite canonical limit
-- ============================================================

#check RHFormalization.buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
#check RHFormalization.detailedConstructionFromFiniteCanonicalLimit_h_Bcan_matches_shared

#print axioms RHFormalization.buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit
#print axioms RHFormalization.detailedConstructionFromFiniteCanonicalLimit_h_Bcan_matches_shared

-- ============================================================
-- Canonical prime-power finite-to-limit chain
-- ============================================================

#check RHFormalization.CanonicalPrimePowerExhaustionData
#check RHFormalization.CanonicalPrimePowerSeriesData
#check RHFormalization.CanonicalPrimePowerKernelSeriesData
#check RHFormalization.CanonicalPrimePowerIndexKernelSeriesData
#check RHFormalization.CanonicalPrimePowerTsumKernelSeriesData
#check RHFormalization.CanonicalPrimePowerConcreteTsumKernelSeriesData
#check RHFormalization.CanonicalPrimePowerMajorantKernelSeriesData
#check RHFormalization.CanonicalPrimePowerAsymptoticKernelMajorantData
#check RHFormalization.CanonicalPrimePowerKernelErrorBoundData
#check RHFormalization.CanonicalPrimePowerFiniteKernelErrorData
#check RHFormalization.CanonicalPrimePowerSummedKernelErrorData
#check RHFormalization.CanonicalPrimePowerActualKernelErrorData
#check RHFormalization.CanonicalPrimePowerWindowMassErrorData
#check RHFormalization.CanonicalPrimePowerUniformWindowErrorData
#check RHFormalization.CanonicalPrimePowerSharedKernelMajorantData
#check RHFormalization.CanonicalPrimePowerProductWindowErrorData
#check RHFormalization.CanonicalPrimePowerMassGrowthWindowData

-- Most recent reduction endpoint:
#check RHFormalization.weightC_window_product_tendsto_zero_of_massGrowth
#check RHFormalization.buildDBcanLimitDataFromCanonicalPrimePowerMassGrowthWindow
#check RHFormalization.canonicalPrimePowerMassGrowthWindow_h_Bcan_matches_tsum

#print axioms RHFormalization.weightC_window_product_tendsto_zero_of_massGrowth
#print axioms RHFormalization.buildDBcanLimitDataFromCanonicalPrimePowerMassGrowthWindow
#print axioms RHFormalization.canonicalPrimePowerMassGrowthWindow_h_Bcan_matches_tsum

-- Previous product/window layer:
#check RHFormalization.actual_kernel_error_sum_tendsto_zero_of_weightC_window_product
#check RHFormalization.buildDBcanLimitDataFromCanonicalPrimePowerProductWindowError
#check RHFormalization.canonicalPrimePowerProductWindowError_h_Bcan_matches_tsum

#print axioms RHFormalization.actual_kernel_error_sum_tendsto_zero_of_weightC_window_product
#print axioms RHFormalization.buildDBcanLimitDataFromCanonicalPrimePowerProductWindowError
#print axioms RHFormalization.canonicalPrimePowerProductWindowError_h_Bcan_matches_tsum

-- Concrete finite-sum / norm-bound lemmas:
#check RHFormalization.finiteCanonicalPrimePowerPackage_kernel_error_norm_le_of_termError_sum
#check RHFormalization.complex_tendsto_zero_of_norm_bound
#check RHFormalization.real_tendsto_zero_of_nonneg_bound
#check RHFormalization.weighted_kernel_error_norm_le_weight_norm_mul
#check RHFormalization.weighted_shared_kernel_norm_le_weight_norm_mul_majorant

#print axioms RHFormalization.finiteCanonicalPrimePowerPackage_kernel_error_norm_le_of_termError_sum
#print axioms RHFormalization.complex_tendsto_zero_of_norm_bound
#print axioms RHFormalization.real_tendsto_zero_of_nonneg_bound
#print axioms RHFormalization.weighted_kernel_error_norm_le_weight_norm_mul
#print axioms RHFormalization.weighted_shared_kernel_norm_le_weight_norm_mul_majorant
