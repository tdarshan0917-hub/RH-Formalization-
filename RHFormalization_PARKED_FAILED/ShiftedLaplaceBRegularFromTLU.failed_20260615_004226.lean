import RHFormalization.ShiftedLaplaceOmegaGeometry
import RHFormalization.ShiftedLaplaceRegularFromZeroDensity
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# RHFormalization.ShiftedLaplaceBRegularFromTLU

Final finite-to-tsum analytic lift for the shifted/Laplace B-regular branch.

Already banked:
- atomic shifted/Laplace term holomorphy;
- finite shifted/Laplace package holomorphy;
- sqrt branch control;
- Ω-shift geometry.

This file proves:

  local uniform convergence of finite shifted/Laplace canonical packages to
  `(shiftedLaplacePrimePackageAt sigma0).Bshared`
  ⇒ shifted/Laplace `hB_regular`.

It does not prove the M-test/envelope itself. That is the next concrete analytic input.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Local uniform convergence of finite shifted/Laplace packages to the shifted/Laplace
`Bshared` function implies `Bshared` is holomorphic at every point of Ω.
-/
theorem shiftedLaplace_Bshared_holomorphicAt_of_tlu
    (sigma0 : ℝ)
    (h_tlu :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Filter.atTop
        Ω)
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    HolomorphicAtC
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      z := by
  have hdiff_finite_eventually :
      ∀ᶠ I in (Filter.atTop : Filter (Finset PrimePowerPair)),
        DifferentiableOn ℂ
          (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
          Ω := by
    exact Filter.Eventually.of_forall (fun I => by
      intro w hwΩ
      have hAt :
          HolomorphicAtC
            (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
            w :=
        finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
          I w hwΩ
      exact hAt.differentiableAt.differentiableWithinAt)

  have hdiff :
      DifferentiableOn ℂ
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Ω := by
    exact h_tlu.differentiableOn isOpen_Omega_proved hdiff_finite_eventually

  exact (hdiff.analyticOnNhd isOpen_Omega_proved) z hzΩ

/--
The exact `hB_regular` input needed by
`shiftedLaplace_holo_from_cancellation_Bregular_zeroDensity`.
The witness-avoidance hypothesis is irrelevant for the prime side.
-/
theorem shiftedLaplace_Bregular_from_tlu
    (sigma0 : ℝ)
    (h_tlu :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Filter.atTop
        Ω) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC
          (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
          z := by
  intro z hzΩ _hnotW
  exact shiftedLaplace_Bshared_holomorphicAt_of_tlu sigma0 h_tlu z hzΩ

/--
Composition theorem: after zero-density and witness cancellation, the only
remaining shifted-prime regularity input is the local uniform convergence of
finite shifted/Laplace prime packages to their tsum-defined Bshared.
-/
theorem shiftedLaplace_holo_from_cancellation_zeroDensity_tlu
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
    (h_tlu :
      TendstoLocallyUniformlyOn
        (fun I : Finset PrimePowerPair =>
          finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        Filter.atTop
        Ω) :
    HolomorphicOnC (shiftedLaplaceAppendixHFunction sigma0) Ω :=
  shiftedLaplace_holo_from_cancellation_Bregular_zeroDensity
    sigma0
    hsum
    ZF
    hcancel
    (shiftedLaplace_Bregular_from_tlu sigma0 h_tlu)

#print axioms shiftedLaplace_Bshared_holomorphicAt_of_tlu
#print axioms shiftedLaplace_Bregular_from_tlu
#print axioms shiftedLaplace_holo_from_cancellation_zeroDensity_tlu

end

end RHFormalization
