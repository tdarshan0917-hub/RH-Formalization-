import RHFormalization.AppendixELocalBridgeCore

/-!
# RHFormalization.AppendixESharedCanonicalPackage

Appendix-E shared canonical package target.

This file does not create a new RH endpoint.

It isolates the true remaining Appendix-E task: proving that the D-side canonical
package and the H-side zero package are the same shared canonical package on a
common right half-plane.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Evidence that the D-side package and H-side package both agree with one shared
canonical package on a common right half-plane.
-/
structure SharedCanonicalPackageEvidence
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI) where
  Bshared : ℂ → ℂ
  sigma : ℝ
  hsigma_ge_D : D.sigma0 ≤ sigma
  hsigma_ge_H : H.sigma0 ≤ sigma
  h_D_matches_shared :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      D.B s = Bshared s
  h_H_matches_shared :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      H.Bzero s = Bshared s

/--
If both D and H agree with the same shared canonical package, then the formal
Appendix-E interface bridge follows.
-/
def buildInterfaceBridgeFromSharedCanonicalPackage
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (S : SharedCanonicalPackageEvidence D H) :
    InterfaceBridgeAPI D H :=
  { sigma := S.sigma
    hsigma_ge_D := S.hsigma_ge_D
    hsigma_ge_H := S.hsigma_ge_H
    h_interface := by
      intro s hs
      exact
        (S.h_D_matches_shared s hs).trans
          (S.h_H_matches_shared s hs).symm }

/--
Exact current Appendix-E target for the final RH spine.

This is what remains to be constructed from the actual D and H packages.
-/
abbrev AppendixESharedCanonicalPackageTarget
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles) : Type :=
  SharedCanonicalPackageEvidence
    Y.toOperatorResolventBridge
    X.toLegacyZeroPolePackageAPI

end

end RHFormalization
