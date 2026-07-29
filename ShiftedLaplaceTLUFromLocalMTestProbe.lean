import RHFormalization.ShiftedLaplaceBRegularFromTLU
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
Scratch probe.

Goal:
  local M-test envelopes on an open cover of Ω
  ⇒ TendstoLocallyUniformlyOn finite shifted/Laplace packages to Bshared on Ω.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

structure ShiftedLaplaceLocalMTestDataProbe : Type 1 where
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

#check tendstoUniformlyOn_tsum
#check TendstoUniformlyOn.tendstoLocallyUniformlyOn
#check TendstoLocallyUniformlyOn.mono
#check tendstoLocallyUniformlyOn_iUnion
#check shiftedLaplace_holo_from_cancellation_zeroDensity_tlu

theorem shiftedLaplace_tlu_from_local_mtest_probe
    (sigma0 : ℝ)
    (D : ShiftedLaplaceLocalMTestDataProbe) :
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

end

end RHFormalization
