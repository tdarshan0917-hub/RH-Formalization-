import RHFormalization.ShiftedLaplaceTLUFromLocalMTest
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# RHFormalization.ShiftedLaplaceAbsConvMTest

Firewall for the shifted/Laplace prime-side M-test.

Already banked:
- finite shifted/Laplace packages are holomorphic on Ω;
- local M-test data on Ω would imply the shifted/Laplace h_holo input.

This file records the correct absolute-convergence region for the raw
shifted/Laplace prime series and banks the one-patch/open-cover M-test
constructor on that region.

It deliberately does NOT claim a global M-test on all Ω.
The full-Ω h_holo must use the Appendix-H continuation/cancellation package.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Candidate absolute-convergence region for the raw shifted/Laplace prime series.

Heuristic:
  term ~ Λ(q) q^(-(1/2 + Re sqrt(s+1/4)))
so absolute convergence wants `Re sqrt(s+1/4) > 1/2`.
-/
abbrev shiftedLaplaceAbsConvRegion : Set ℂ :=
  {s : ℂ | (1 / 2 : ℝ) < (shiftedLaplaceSqrt s).re}

/--
One-patch M-test data for the shifted/Laplace weighted prime series.
-/
structure ShiftedLaplaceOnePatchMTestData (U : Set ℂ) : Type 1 where
  u : PrimePowerPair → ℝ
  h_summable : Summable u
  h_bound :
    ∀ q : PrimePowerPair,
    ∀ s : ℂ,
      s ∈ U →
        ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ ≤ u q

/--
On a single patch, a summable majorant gives uniform convergence of finite
shifted/Laplace packages to the raw shifted/Laplace prime-power tsum.
-/
theorem shiftedLaplace_tendstoUniformlyOn_of_one_patch_mtest
    (U : Set ℂ)
    (D : ShiftedLaplaceOnePatchMTestData U) :
    TendstoUniformlyOn
      (fun I : Finset PrimePowerPair =>
        finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      (fun s : ℂ =>
        ∑' q : PrimePowerPair,
          q.weightC * shiftedLaplaceHeatKernelC q.center s)
      Filter.atTop
      U := by
  simpa [finiteCanonicalPrimePowerPackage] using
    (tendstoUniformlyOn_tsum
      D.h_summable
      D.h_bound)

/--
One-patch M-test data gives local-uniform convergence on that patch.
-/
theorem shiftedLaplace_tendstoLocallyUniformlyOn_of_one_patch_mtest
    (U : Set ℂ)
    (D : ShiftedLaplaceOnePatchMTestData U) :
    TendstoLocallyUniformlyOn
      (fun I : Finset PrimePowerPair =>
        finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      (fun s : ℂ =>
        ∑' q : PrimePowerPair,
          q.weightC * shiftedLaplaceHeatKernelC q.center s)
      Filter.atTop
      U :=
  (shiftedLaplace_tendstoUniformlyOn_of_one_patch_mtest U D).tendstoLocallyUniformlyOn

/--
Open-cover M-test data on the absolute-convergence region.
-/
structure ShiftedLaplaceAbsConvLocalMTestData : Type 1 where
  U : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion} → Set ℂ
  hU_open : ∀ z : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion}, IsOpen (U z)
  hU_cover :
    shiftedLaplaceAbsConvRegion ⊆
      ⋃ z : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion}, U z
  patch :
    ∀ z : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion},
      ShiftedLaplaceOnePatchMTestData (U z)

/--
Local M-test data on the absolute-convergence region gives local-uniform
convergence of finite shifted/Laplace packages to the shifted/Laplace Bshared
tsum on that region.
-/
theorem shiftedLaplace_tlu_on_absConvRegion_from_local_mtest
    (sigma0 : ℝ)
    (D : ShiftedLaplaceAbsConvLocalMTestData) :
    TendstoLocallyUniformlyOn
      (fun I : Finset PrimePowerPair =>
        finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      Filter.atTop
      shiftedLaplaceAbsConvRegion := by
  have h_each :
      ∀ z0 : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion},
        TendstoLocallyUniformlyOn
          (fun I : Finset PrimePowerPair =>
            finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC * shiftedLaplaceHeatKernelC q.center s)
          Filter.atTop
          (D.U z0) := by
    intro z0
    exact shiftedLaplace_tendstoLocallyUniformlyOn_of_one_patch_mtest
      (D.U z0)
      (D.patch z0)

  have h_union :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ =>
          ∑' q : PrimePowerPair,
            q.weightC * shiftedLaplaceHeatKernelC q.center s)
        Filter.atTop
        (⋃ z0 : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion}, D.U z0) :=
    tendstoLocallyUniformlyOn_iUnion D.hU_open h_each

  have h_region :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ =>
          ∑' q : PrimePowerPair,
            q.weightC * shiftedLaplaceHeatKernelC q.center s)
        Filter.atTop
        shiftedLaplaceAbsConvRegion :=
    h_union.mono D.hU_cover

  simpa [shiftedLaplacePrimePackageAt, canonicalPrimePowerPackageFromKernelTsum] using h_region

#print axioms shiftedLaplaceAbsConvRegion
#print axioms ShiftedLaplaceOnePatchMTestData
#print axioms shiftedLaplace_tendstoUniformlyOn_of_one_patch_mtest
#print axioms shiftedLaplace_tendstoLocallyUniformlyOn_of_one_patch_mtest
#print axioms ShiftedLaplaceAbsConvLocalMTestData
#print axioms shiftedLaplace_tlu_on_absConvRegion_from_local_mtest

end

end RHFormalization
