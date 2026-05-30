import RHFormalization.CanonicalPrimePowerConcreteTsumPackage
import RHFormalization.BsharedPrincipalPartAtWitness
import RHFormalization.CanonicalPrimePowerTsumSeries

/-!
# RHFormalization.CanonicalPrimePowerTsumPrincipalPart

Principal-part bridge for the concrete tsum-defined canonical prime-power package.

The witness-cancellation branch now needs:

  HasPrincipalPartAtC
    Y.B.Cshared.Bshared
    W.s0
    (-(groupedResidueCoeff M (groupedClass W))).

This file moves that obligation upstream to the actual tsum expression defining
the concrete canonical package:

  fun s => ∑' q, q.weightC * Kshared q.center s.

It does not prove the hard tsum principal-part theorem; it makes that theorem
the exact remaining source obligation.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the concrete prime-power tsum has a principal part at a witness, then the
`Bshared` field of `canonicalPrimePowerPackageFromKernelTsum` has the same
principal part.
-/
theorem canonicalPrimePowerPackageFromKernelTsum_principalPart_at_witness
    (sigma0 : ℝ)
    (Kshared : CanonicalKernelC)
    (W : ZeroWitness)
    (c : ℂ)
    (hpp :
      HasPrincipalPartAtC
        (fun s : ℂ =>
          ∑' q : PrimePowerPair,
            q.weightC * Kshared q.center s)
        W.s0
        c) :
    HasPrincipalPartAtC
      (canonicalPrimePowerPackageFromKernelTsum sigma0 Kshared).Bshared
      W.s0
      c := by
  simpa [canonicalPrimePowerPackageFromKernelTsum] using hpp

/--
The exact opposite-principal-part theorem needed for a concrete tsum-defined
canonical package.
-/
theorem canonicalPrimePowerPackageFromKernelTsum_oppositePrincipalPart_at_witness
    (sigma0 : ℝ)
    (Kshared : CanonicalKernelC)
    (M : ZeroMultiplicityData)
    (groupedClass :
      ∀ W : ZeroWitness, GroupedPoleClass M W)
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC * Kshared q.center s)
          W.s0
          (-(groupedResidueCoeff M (groupedClass W))))
    (W : ZeroWitness) :
    HasPrincipalPartAtC
      (canonicalPrimePowerPackageFromKernelTsum sigma0 Kshared).Bshared
      W.s0
      (-(groupedResidueCoeff M (groupedClass W))) :=
  canonicalPrimePowerPackageFromKernelTsum_principalPart_at_witness
    sigma0
    Kshared
    W
    (-(groupedResidueCoeff M (groupedClass W)))
    (h_tsum_principalPart W)

/--
Build `BsharedOppositePrincipalPartData` for a selected D construction whose
shared package is the concrete tsum-defined package.
-/
def BsharedOppositePrincipalPartData_of_tsum_principalParts
    (Y : DDetailedConstructionWithOperatorLegality)
    (sigma0 : ℝ)
    (Kshared : CanonicalKernelC)
    (M : ZeroMultiplicityData)
    (groupedClass :
      ∀ W : ZeroWitness, GroupedPoleClass M W)
    (hC :
      Y.B.Cshared =
        canonicalPrimePowerPackageFromKernelTsum sigma0 Kshared)
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC * Kshared q.center s)
          W.s0
          (-(groupedResidueCoeff M (groupedClass W)))) :
    BsharedOppositePrincipalPartData Y M :=
{ groupedClass := groupedClass
  h_Bshared_principalPart := by
    intro W
    simpa [hC] using
      canonicalPrimePowerPackageFromKernelTsum_oppositePrincipalPart_at_witness
        sigma0
        Kshared
        M
        groupedClass
        h_tsum_principalPart
        W }

end

end RHFormalization
