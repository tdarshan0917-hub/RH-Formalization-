import RHFormalization.ShiftedLaplaceBRegularFromTLU
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# RHFormalization.ShiftedLaplaceTLUFromLocalMTest

This file banks the M-test constructor for the remaining shifted/Laplace
prime-side local-uniform convergence input.

Already banked:
- finite shifted/Laplace packages are holomorphic on Ω;
- local-uniform convergence of those finite packages to Bshared implies
  `hB_regular`;
- `hB_regular + hcancel + hsum + ZF` implies shifted/Laplace `h_holo`.

This file proves:

  local summable M-test envelope on an open cover of Ω
  ⇒ the required `h_tlu`.

The next analytic target after this is the actual shifted/Laplace envelope estimate.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Local M-test data for the shifted/Laplace prime-power series.

For every point of Ω, we choose an open set `U z0` covering that point region,
plus a summable majorant for the shifted/Laplace weighted terms on that open set.
-/
structure ShiftedLaplaceLocalMTestData : Type 1 where
  U : {z : ℂ // z ∈ Ω} → Set ℂ
  hU_open : ∀ z : {z : ℂ // z ∈ Ω}, IsOpen (U z)
  hU_cover : Ω ⊆ ⋃ z : {z : ℂ // z ∈ Ω}, U z
  u : {z : ℂ // z ∈ Ω} → PrimePowerPair → ℝ
  h_summable : ∀ z : {z : ℂ // z ∈ Ω}, Summable (u z)
  h_bound :
    ∀ z0 : {z : ℂ // z ∈ Ω},
    ∀ q : PrimePowerPair,
    ∀ s : ℂ,
      s ∈ U z0 →
        ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ ≤ u z0 q

/--
Local M-test data gives the exact local-uniform convergence input required by
`shiftedLaplace_Bregular_from_tlu`.
-/
theorem shiftedLaplace_tlu_from_local_mtest
    (sigma0 : ℝ)
    (D : ShiftedLaplaceLocalMTestData) :
    TendstoLocallyUniformlyOn
      (fun I : Finset PrimePowerPair =>
        finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      Filter.atTop
      Ω := by
  have h_each :
      ∀ z0 : {z : ℂ // z ∈ Ω},
        TendstoLocallyUniformlyOn
          (fun I : Finset PrimePowerPair =>
            finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC * shiftedLaplaceHeatKernelC q.center s)
          Filter.atTop
          (D.U z0) := by
    intro z0
    have h_uniform :
        TendstoUniformlyOn
          (fun I : Finset PrimePowerPair =>
            finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC * shiftedLaplaceHeatKernelC q.center s)
          Filter.atTop
          (D.U z0) := by
      simpa [finiteCanonicalPrimePowerPackage] using
        (tendstoUniformlyOn_tsum
          (D.h_summable z0)
          (D.h_bound z0))
    exact h_uniform.tendstoLocallyUniformlyOn

  have h_union :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ =>
          ∑' q : PrimePowerPair,
            q.weightC * shiftedLaplaceHeatKernelC q.center s)
        Filter.atTop
        (⋃ z0 : {z : ℂ // z ∈ Ω}, D.U z0) :=
    tendstoLocallyUniformlyOn_iUnion D.hU_open h_each

  have h_omega :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ =>
          ∑' q : PrimePowerPair,
            q.weightC * shiftedLaplaceHeatKernelC q.center s)
        Filter.atTop
        Ω :=
    h_union.mono D.hU_cover

  simpa [shiftedLaplacePrimePackageAt, canonicalPrimePowerPackageFromKernelTsum] using h_omega

/--
The prime-side `hB_regular` input follows from local M-test data.
-/
theorem shiftedLaplace_Bregular_from_local_mtest
    (sigma0 : ℝ)
    (D : ShiftedLaplaceLocalMTestData) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC
          (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
          z :=
  shiftedLaplace_Bregular_from_tlu
    sigma0
    (shiftedLaplace_tlu_from_local_mtest sigma0 D)

/--
Composition theorem: after zero-density and witness cancellation, local M-test
data is enough to close the shifted/Laplace `h_holo`.
-/
theorem shiftedLaplace_holo_from_cancellation_zeroDensity_localMTest
    (sigma0 : ℝ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts)
    (hcancel :
      ∀ W : ZeroWitness,
        ShiftedLaplaceWitnessCancellationData sigma0 W)
    (D : ShiftedLaplaceLocalMTestData) :
    HolomorphicOnC (shiftedLaplaceAppendixHFunction sigma0) Ω :=
  shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
    sigma0
    hsum
    ZF
    hcancel
    (shiftedLaplace_tlu_from_local_mtest sigma0 D)

#print axioms ShiftedLaplaceLocalMTestData
#print axioms shiftedLaplace_tlu_from_local_mtest
#print axioms shiftedLaplace_Bregular_from_local_mtest
#print axioms shiftedLaplace_holo_from_cancellation_zeroDensity_localMTest

end

end RHFormalization
