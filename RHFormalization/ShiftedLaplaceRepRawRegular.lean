import RHFormalization.ShiftedLaplaceRepDirectPackage
import RHFormalization.ShiftedLaplaceBRegularFromTLU
import RHFormalization.ShiftedLaplaceTLUFromLocalMTest
import RHFormalization.ShiftedLaplaceRegularFromZeroDensity
import RHFormalization.ExplicitFormulaRegularBranch
import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.EnvelopeFromZeroDensity
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/--
Safe regularity provider for the actual corrected representative raw function.

This uses the definitional identity

  repRaw sigma0 s =
    (shiftedLaplacePrimePackageAt sigma0).Bshared s
      + ZpoleRepSeries defaultZeroMultiplicityData s

and proves holomorphy off witness poles from:
  * Bshared regularity,
  * representative Z-pole regularity away from ZeroPoleSet.
-/
theorem repRaw_h_regular_from_Bregular
    (ZF : ZetaZeroFacts)
    (sigma0 : ℝ)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
            z) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC (repRaw sigma0) z := by
  intro z hzΩ hnot
  have hB :
      HolomorphicAtC
        (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        z :=
    hB_regular z hzΩ hnot
  have hZ :
      HolomorphicAtC
        (ZpoleRepSeries defaultZeroMultiplicityData)
        z := by
    exact
      repZpole_analyticAt_nonpole
        defaultZeroMultiplicityData
        (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional)
        z
        hzΩ
        (not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hnot)
  simpa [repRaw] using hB.add hZ

/-- Concrete `sigma0 = 1` wrapper. -/
theorem repRaw_one_h_regular_from_Bregular
    (ZF : ZetaZeroFacts)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
            z) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        HolomorphicAtC (repRaw 1) z :=
  repRaw_h_regular_from_Bregular ZF 1 hB_regular

#print axioms repRaw_h_regular_from_Bregular
#print axioms repRaw_one_h_regular_from_Bregular

end
end RHFormalization
