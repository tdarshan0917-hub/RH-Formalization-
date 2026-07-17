import RHFormalization.ShiftedLaplaceHoloFromCancellation
import RHFormalization.ExplicitFormulaRegularBranch
import RHFormalization.EnvelopeFromZeroDensity
import RHFormalization.ZpoleFromSeries

/-!
# RHFormalization.ShiftedLaplaceRegularFromZeroDensity

This file removes the Zpole side from the shifted/Laplace regular-branch input.

Already banked:
  hcancel + h_regular ⇒ shifted/Laplace h_holo.

This file proves:
  hsum + ZF + shifted-prime-B-regular ⇒ h_regular.

So after this file, the shifted/Laplace H-side is reduced to:
  1. witness cancellation data;
  2. regular holomorphy of the shifted prime package itself.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- Default Zpole convergence produced from the zero-density summability input. -/
def shiftedLaplaceDefaultZpoleConvFromZeroDensity
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2))) :
    ZeroPoleLocalUniformConvergenceAPI
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData) :=
  buildZeroPoleLUCAPIFromEnvelope
    defaultZeroMultiplicityData
    (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum)

/--
Away from witness pole-points inside Ω, the default ZpoleSeries is holomorphic.
-/
theorem shiftedLaplace_zpole_regular_from_zeroDensity
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC (ZpoleSeries defaultZeroMultiplicityData) z := by
  intro z hzΩ hnotW
  have hznp : z ∉ ZeroPoleSet :=
    not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hnotW
  simpa [HolomorphicAtC] using
    (zpole_analyticAt_nonpole
      defaultZeroMultiplicityData
      (ZpoleSeries defaultZeroMultiplicityData)
      (shiftedLaplaceDefaultZpoleConvFromZeroDensity hsum)
      z
      hzΩ
      hznp)

/--
The shifted/Laplace regular branch follows from regular holomorphy of the
shifted prime package plus the already-controlled Zpole regularity.
-/
theorem shiftedLaplace_regular_from_Bregular_zeroDensity
    (sigma0 : ℝ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
            z) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z := by
  intro z hzΩ hnotW
  have hB :
      HolomorphicAtC
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        z :=
    hB_regular z hzΩ hnotW
  have hZ :
      HolomorphicAtC (ZpoleSeries defaultZeroMultiplicityData) z :=
    shiftedLaplace_zpole_regular_from_zeroDensity hsum ZF z hzΩ hnotW
  simpa [shiftedLaplaceAppendixHFunction] using hB.add hZ

/--
Shifted/Laplace h_holo from witness cancellation plus shifted-prime regularity.
-/
theorem shiftedLaplace_holo_from_cancellation_Bregular_zeroDensity
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
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
            z) :
    HolomorphicOnC (shiftedLaplaceAppendixHFunction sigma0) Ω :=
  shiftedLaplace_holo_from_cancellation_and_regular
    sigma0
    hcancel
    (shiftedLaplace_regular_from_Bregular_zeroDensity
      sigma0 hsum ZF hB_regular)

/--
Build the shifted/Laplace Harch package from cancellation data and shifted-prime regularity.
-/
def shiftedLaplaceHarchPackageFromCancellationBregularZeroDensity
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
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
            z) :
    HArchPackage :=
  shiftedLaplaceHarchPackageFromCancellationAndRegular
    sigma0
    hcancel
    (shiftedLaplace_regular_from_Bregular_zeroDensity
      sigma0 hsum ZF hB_regular)

/--
The shifted/Laplace split from cancellation data and shifted-prime regularity.
-/
theorem shiftedLaplaceHarchPackageFromCancellationBregularZeroDensity_split
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
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
            z)
    (s : ℂ) :
    s ∈ RightHalfPlane sigma0 →
      (shiftedLaplacePrimePackageAt sigma0).Bshared s =
        (shiftedLaplaceHarchPackageFromCancellationBregularZeroDensity
          sigma0 hsum ZF hcancel hB_regular).Harch s
          - ZpoleSeries defaultZeroMultiplicityData s := by
  intro hs
  exact
    shiftedLaplaceHarchPackageFromCancellationAndRegular_split
      sigma0
      hcancel
      (shiftedLaplace_regular_from_Bregular_zeroDensity
        sigma0 hsum ZF hB_regular)
      s
      hs

#print axioms shiftedLaplaceDefaultZpoleConvFromZeroDensity
#print axioms shiftedLaplace_zpole_regular_from_zeroDensity
#print axioms shiftedLaplace_regular_from_Bregular_zeroDensity
#print axioms shiftedLaplace_holo_from_cancellation_Bregular_zeroDensity
#print axioms shiftedLaplaceHarchPackageFromCancellationBregularZeroDensity
#print axioms shiftedLaplaceHarchPackageFromCancellationBregularZeroDensity_split

end

end RHFormalization
