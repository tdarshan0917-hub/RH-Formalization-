import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.CanonicalPrimePowerTsumPrincipalPart
import RHFormalization.BsharedPrincipalPartAtWitness
import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts

/-!
# RHFormalization.ShiftedLaplaceWitnessCancellationFromPrincipalParts

Builds the exact `ShiftedLaplaceWitnessCancellationData` object from
opposite principal parts.

This does not prove the hard shifted/Laplace B-side principal part.
It isolates the remaining analytic input precisely.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Generic constructor: if `B` has principal part `-c/(s-W.s0)` and `Z` has
principal part `c/(s-W.s0)`, plus the center-value compatibility, then we get
`WitnessCancellationData B Z W`.

This returns data, so it is a `def`, not a `theorem`.
-/
def witnessCancellationData_from_opposite_principalParts
    (B Z : ℂ → ℂ)
    (W : ZeroWitness)
    (c : ℂ)
    (hBpp :
      HasPrincipalPartAtC
        B
        W.s0
        (-c))
    (hZpp :
      HasPrincipalPartAtC
        Z
        W.s0
        c)
    (hpoint :
      (Classical.choose hBpp) W.s0 +
        (Classical.choose hZpp) W.s0 =
          B W.s0 + Z W.s0) :
    WitnessCancellationData B Z W := by
  classical
  have hBspec := Classical.choose_spec hBpp
  have hZspec := Classical.choose_spec hZpp
  refine
    { coeff := c
      hB := Classical.choose hBpp
      hZ := Classical.choose hZpp
      hB_holo := ?_
      hZ_holo := ?_
      hB_pp := ?_
      hZ_pp := ?_
      hpoint := ?_ }
  · exact hBspec.1
  · exact hZspec.1
  · exact hBspec.2
  · exact hZspec.2
  · exact hpoint

/--
Shifted/Laplace specialization for one witness.
-/
def shiftedLaplaceWitnessCancellationData_from_opposite_principalParts
    (sigma0 : ℝ)
    (W : ZeroWitness)
    (c : ℂ)
    (hBpp :
      HasPrincipalPartAtC
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        W.s0
        (-c))
    (hZpp :
      HasPrincipalPartAtC
        (ZpoleSeries defaultZeroMultiplicityData)
        W.s0
        c)
    (hpoint :
      (Classical.choose hBpp) W.s0 +
        (Classical.choose hZpp) W.s0 =
          (shiftedLaplacePrimePackageAt sigma0).Bshared W.s0 +
            ZpoleSeries defaultZeroMultiplicityData W.s0) :
    ShiftedLaplaceWitnessCancellationData sigma0 W :=
  witnessCancellationData_from_opposite_principalParts
    (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
    (ZpoleSeries defaultZeroMultiplicityData)
    W
    c
    hBpp
    hZpp
    hpoint

/--
Global `hcancel` constructor from grouped B/Z principal parts.

This is the exact bridge we need before attacking the remaining analytic theorem:
the shifted/Laplace prime-power tsum has the required B-side opposite principal part.
-/
def shiftedLaplace_hcancel_from_grouped_principalParts
    (sigma0 : ℝ)
    (groupedClass :
      ∀ W : ZeroWitness,
        GroupedPoleClass defaultZeroMultiplicityData W)
    (hBpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
          W.s0
          (-(groupedResidueCoeff defaultZeroMultiplicityData (groupedClass W))))
    (hZpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (ZpoleSeries defaultZeroMultiplicityData)
          W.s0
          (groupedResidueCoeff defaultZeroMultiplicityData (groupedClass W)))
    (hpoint :
      ∀ W : ZeroWitness,
        (Classical.choose (hBpp W)) W.s0 +
          (Classical.choose (hZpp W)) W.s0 =
            (shiftedLaplacePrimePackageAt sigma0).Bshared W.s0 +
              ZpoleSeries defaultZeroMultiplicityData W.s0) :
    ∀ W : ZeroWitness,
      ShiftedLaplaceWitnessCancellationData sigma0 W := by
  intro W
  exact
    shiftedLaplaceWitnessCancellationData_from_opposite_principalParts
      sigma0
      W
      (groupedResidueCoeff defaultZeroMultiplicityData (groupedClass W))
      (hBpp W)
      (hZpp W)
      (hpoint W)

#print axioms witnessCancellationData_from_opposite_principalParts
#print axioms shiftedLaplaceWitnessCancellationData_from_opposite_principalParts
#print axioms shiftedLaplace_hcancel_from_grouped_principalParts

end

end RHFormalization
