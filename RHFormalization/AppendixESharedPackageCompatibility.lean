import RHFormalization.OmegaMeromorphicZeroPropagationClopen
import RHFormalization.AppendixESharedPackageObligations

/-!
# RHFormalization.AppendixESharedPackageCompatibility

Appendix-E bridge from strengthened D/H shared-package evidence.

This file uses the new fields:

* `DBcanLimitData.h_Bcan_matches_shared`;
* `HSideOverlapPackage.h_Bzero_matches_shared`.

The only remaining compatibility input is that the D-side and H-side `Cshared`
objects are the same canonical prime-power package.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
The remaining Appendix-E compatibility condition after strengthening the D/H
package structures.

It says the D-side and H-side shared canonical packages are literally the same
canonical package.
-/
structure AppendixESharedPackageCompatibility
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles) : Prop where
  h_Cshared_eq :
    X.layer.overlap.Cshared = Y.B.Cshared

/--
Extract D-side matching evidence from the strengthened D package.
-/
def buildDMatchesSharedCanonicalPackageFromDetailed
    (Y : DDetailedConstructionWithOperatorLegality) :
    DMatchesSharedCanonicalPackage
      Y.toOperatorResolventBridge
      Y.B.Cshared :=
  { sigma := Y.toOperatorResolventBridge.sigma0
    hsigma_ge_D := le_rfl
    hsigma_ge_C := by
      simpa using Y.B.h_Cshared_sigma_le
    h_D_matches := by
      intro s hs
      simpa using Y.B.h_Bcan_matches_shared s hs }

/--
Extract H-side matching evidence from the strengthened H package, rewritten
against the D-side `Cshared` using compatibility.
-/
def buildHMatchesSharedCanonicalPackageFromCompatibility
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (S : AppendixESharedPackageCompatibility Y X) :
    HMatchesSharedCanonicalPackage
      X.toLegacyZeroPolePackageAPI
      Y.B.Cshared :=
  { sigma := X.toLegacyZeroPolePackageAPI.sigma0
    hsigma_ge_H := le_rfl
    hsigma_ge_C := by
      simpa [S.h_Cshared_eq] using X.layer.overlap.h_Cshared_sigma_le
    h_H_matches := by
      intro s hs
      simpa [S.h_Cshared_eq] using
        X.layer.overlap.h_Bzero_matches_shared s (by simpa using hs) }

/--
Build the formal Appendix-E bridge from strengthened D/H package data plus
shared-package compatibility.
-/
def buildInterfaceBridgeFromSharedPackageCompatibility
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (S : AppendixESharedPackageCompatibility Y X) :
    InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI :=
  buildInterfaceBridgeFromSharedCanonicalMatches
    Y.toOperatorResolventBridge
    X.toLegacyZeroPolePackageAPI
    Y.B.Cshared
    (buildDMatchesSharedCanonicalPackageFromDetailed Y)
    (buildHMatchesSharedCanonicalPackageFromCompatibility Y X S)

/--
RH spine after replacing the Appendix-E bridge input by the single
shared-package compatibility condition.
-/
theorem finalRHSpine_after_sharedPackageCompatibility
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (S : AppendixESharedPackageCompatibility Y X) :
    RiemannHypothesis :=
  finalRHSpine_after_zeroPropagation
    ZF
    Y
    X
    (buildInterfaceBridgeFromSharedPackageCompatibility Y X S)

end


/-!
## Compatibility from direct Cshared equality

This is the sharp Appendix-E target:
prove that the H-side overlap package and the D-side B package use the same
canonical prime-power package.
-/

/--
Build Appendix-E shared-package compatibility from the direct package equality
in the orientation already used by `AppendixESharedPackageCompatibility`.
-/
def buildAppendixESharedPackageCompatibilityFromCsharedEq
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (hC : X.layer.overlap.Cshared = Y.B.Cshared) :
    AppendixESharedPackageCompatibility Y X :=
  { h_Cshared_eq := hC }

/--
Final RH spine from the direct Appendix-E Cshared equality.

This is the current top-level proof ledger:
`ZF`, `Y`, `X`, and `X.layer.overlap.Cshared = Y.B.Cshared` imply RH.
-/
theorem finalRHSpine_after_directCsharedEq
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (hC : X.layer.overlap.Cshared = Y.B.Cshared) :
    RiemannHypothesis :=
  finalRHSpine_after_sharedPackageCompatibility
    ZF
    Y
    X
    (buildAppendixESharedPackageCompatibilityFromCsharedEq Y X hC)

end RHFormalization
