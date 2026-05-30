import RHFormalization.AppendixESharedPackageCompatibility

/-!
# RHFormalization.AppendixESharedPackageFunctionalCompatibility

Function-level Appendix-E shared package compatibility.

The earlier compatibility condition
`X.layer.overlap.Cshared = Y.B.Cshared`
is stronger than necessary.  Appendix E only needs the two shared canonical
package *functions* to agree on a common right half-plane.

This file replaces structure equality by the exact overlap function equality.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Function-level compatibility between the D-side and H-side shared canonical
packages.

This is the exact remaining Appendix-E shared-package identity:
on a common right half-plane, the two `Bshared` functions agree.
-/
structure AppendixESharedPackageFunctionalCompatibility
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles) : Type where
  sigma : ℝ
  hsigma_ge_D :
    Y.toOperatorResolventBridge.sigma0 ≤ sigma
  hsigma_ge_H :
    X.toLegacyZeroPolePackageAPI.sigma0 ≤ sigma
  h_shared_B :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      Y.B.Cshared.Bshared s =
        X.layer.overlap.Cshared.Bshared s

/--
Build the formal Appendix-E bridge from function-level compatibility of the
shared canonical packages.
-/
def buildInterfaceBridgeFromSharedPackageFunctionalCompatibility
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (S : AppendixESharedPackageFunctionalCompatibility Y X) :
    InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI :=
  { sigma := S.sigma
    hsigma_ge_D := S.hsigma_ge_D
    hsigma_ge_H := S.hsigma_ge_H
    h_interface := by
      intro s hs

      have hD :
          Y.toOperatorResolventBridge.B s =
            Y.B.Cshared.Bshared s := by
        simpa using
          Y.B.h_Bcan_matches_shared s
            (RightHalfPlane_subset_of_le S.hsigma_ge_D hs)

      have hH :
          X.toLegacyZeroPolePackageAPI.Bzero s =
            X.layer.overlap.Cshared.Bshared s := by
        simpa using
          X.layer.overlap.h_Bzero_matches_shared s
            (RightHalfPlane_subset_of_le S.hsigma_ge_H hs)

      exact hD.trans ((S.h_shared_B s hs).trans hH.symm) }

/--
RH spine after replacing the Appendix-E bridge input by function-level shared
canonical package compatibility.

Remaining explicit inputs are now:
* `ZF`;
* `Y`;
* `X`;
* function-level Appendix-E shared package compatibility.
-/
theorem finalRHSpine_after_sharedPackageFunctionalCompatibility
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (S : AppendixESharedPackageFunctionalCompatibility Y X) :
    RiemannHypothesis :=
  finalRHSpine_after_zeroPropagation
    ZF
    Y
    X
    (buildInterfaceBridgeFromSharedPackageFunctionalCompatibility Y X S)

end


/-!
## Shared-B identity reduction

This section reduces `AppendixESharedPackageFunctionalCompatibility Y X`
to the single real bridge identity:

  Y.B.Cshared.Bshared s = X.layer.overlap.Cshared.Bshared s

on a common right half-plane.
-/

/--
The common right-half-plane threshold for a D package `Y` and an H package `X`.
-/
def sharedCompatibilitySigma
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles) : ℝ :=
  max Y.toOperatorResolventBridge.sigma0
      X.toLegacyZeroPolePackageAPI.sigma0

/--
Build Appendix-E shared-package compatibility from the single shared-B identity.
-/
def buildAppendixESharedPackageCompatibilityFromBIdentity
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (h_shared_B :
      ∀ s : ℂ,
        s ∈ RightHalfPlane (sharedCompatibilitySigma Y X) →
          Y.B.Cshared.Bshared s =
            X.layer.overlap.Cshared.Bshared s) :
    AppendixESharedPackageFunctionalCompatibility Y X :=
{ sigma := sharedCompatibilitySigma Y X
  hsigma_ge_D := by
    unfold sharedCompatibilitySigma
    exact le_max_left _ _
  hsigma_ge_H := by
    unfold sharedCompatibilitySigma
    exact le_max_right _ _
  h_shared_B := h_shared_B }

/--
Final RH spine reduced to `ZF`, `Y`, `X`, and the shared-B identity.
-/
theorem finalRHSpine_from_sharedBIdentity
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (h_shared_B :
      ∀ s : ℂ,
        s ∈ RightHalfPlane (sharedCompatibilitySigma Y X) →
          Y.B.Cshared.Bshared s =
            X.layer.overlap.Cshared.Bshared s) :
    RiemannHypothesis :=
  finalRHSpine_after_sharedPackageFunctionalCompatibility
    ZF
    Y
    X
    (buildAppendixESharedPackageCompatibilityFromBIdentity
      Y X h_shared_B)


/-!
## Shared-B identity from equality of shared canonical packages

This is the next top-level reduction.  It shows that Appendix-E's real
compatibility field follows immediately if the D-side and H-side packages use
the same `CanonicalPrimePowerPackage`.
-/

/--
The Appendix-E shared-B identity follows from equality of the D-side and H-side
shared canonical packages.
-/
theorem sharedBIdentity_of_Cshared_eq
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (hC : Y.B.Cshared = X.layer.overlap.Cshared) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane (sharedCompatibilitySigma Y X) →
        Y.B.Cshared.Bshared s =
          X.layer.overlap.Cshared.Bshared s := by
  intro s hs
  simpa [hC]

/--
Final RH spine reduced to equality of the D-side and H-side shared canonical
packages.

This is sharper than `h_shared_B`: if both sides are built from the same
`Cshared`, the Appendix-E bridge is automatic.
-/
theorem finalRHSpine_from_Cshared_eq
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (hC : Y.B.Cshared = X.layer.overlap.Cshared) :
    RiemannHypothesis :=
  finalRHSpine_from_sharedBIdentity
    ZF
    Y
    X
    (sharedBIdentity_of_Cshared_eq Y X hC)

end RHFormalization
