import RHFormalization.AppendixESharedPackageFunctionalCompatibility

/-!
# RHFormalization.AppendixESharedPackageCompatibilityFromBIdentity

Appendix-E shared-package compatibility reduced to the single shared-B identity.

This file must never import `RHFormalization`, because it is intended to be
imported by `RHFormalization.lean`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The common right-half-plane threshold for a D package `Y` and an H package `X`.
-/
def sharedCompatibilitySigma
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles) : ℝ :=
  max Y.toOperatorResolventBridge.sigma0
      X.toLegacyZeroPolePackageAPI.sigma0

/--
Build Appendix-E shared-package compatibility from the single real bridge identity.
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

end

end RHFormalization
