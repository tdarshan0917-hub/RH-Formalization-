import RHFormalization.CanonicalPrimePowerPackage
import RHFormalization.AppendixESharedCanonicalPackage

/-!
# RHFormalization.AppendixESharedPackageObligations

Concrete Appendix-E proof obligations.

This file does not create a new RH endpoint.

It states the exact two equations that must be proved to remove the remaining
Appendix-E bridge input:

1. D-side `Bcan` agrees with the shared canonical prime-power package.
2. H-side `Bzero` agrees with the same shared canonical prime-power package.

The current project data has `DBcanLimitData.Bcan` and `HSideOverlapPackage.Bzero`
as opaque fields, so these equations are the missing formal evidence.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
D-side evidence that the exported operator-side package is the shared canonical
prime-power package on a right half-plane.
-/
structure DMatchesSharedCanonicalPackage
    (D : OperatorResolventBridge)
    (C : CanonicalPrimePowerPackage) where
  sigma : ℝ
  hsigma_ge_D : D.sigma0 ≤ sigma
  hsigma_ge_C : C.sigma0 ≤ sigma
  h_D_matches :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      D.B s = C.Bshared s

/--
H-side evidence that the zero-side package is the same shared canonical
prime-power package on a right half-plane.
-/
structure HMatchesSharedCanonicalPackage
    (H : ZeroPolePackageAPI)
    (C : CanonicalPrimePowerPackage) where
  sigma : ℝ
  hsigma_ge_H : H.sigma0 ≤ sigma
  hsigma_ge_C : C.sigma0 ≤ sigma
  h_H_matches :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      H.Bzero s = C.Bshared s

/--
Combine D-side and H-side matching evidence into the shared canonical package
evidence already known to imply `InterfaceBridgeAPI`.
-/
def buildSharedCanonicalPackageEvidenceFromMatches
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (C : CanonicalPrimePowerPackage)
    (DM : DMatchesSharedCanonicalPackage D C)
    (HM : HMatchesSharedCanonicalPackage H C) :
    SharedCanonicalPackageEvidence D H :=
  let sigma := max DM.sigma HM.sigma
  { Bshared := C.Bshared
    sigma := sigma
    hsigma_ge_D :=
      le_trans DM.hsigma_ge_D (le_max_left DM.sigma HM.sigma)
    hsigma_ge_H :=
      le_trans HM.hsigma_ge_H (le_max_right DM.sigma HM.sigma)
    h_D_matches_shared := by
      intro s hs
      exact
        DM.h_D_matches s
          (RightHalfPlane_subset_of_le
            (le_max_left DM.sigma HM.sigma)
            hs)
    h_H_matches_shared := by
      intro s hs
      exact
        HM.h_H_matches s
          (RightHalfPlane_subset_of_le
            (le_max_right DM.sigma HM.sigma)
            hs) }

/--
Build the formal Appendix-E bridge from D/H matching evidence against one shared
canonical package.
-/
def buildInterfaceBridgeFromSharedCanonicalMatches
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (C : CanonicalPrimePowerPackage)
    (DM : DMatchesSharedCanonicalPackage D C)
    (HM : HMatchesSharedCanonicalPackage H C) :
    InterfaceBridgeAPI D H :=
  buildInterfaceBridgeFromSharedCanonicalPackage
    D
    H
    (buildSharedCanonicalPackageEvidenceFromMatches D H C DM HM)

end

end RHFormalization
