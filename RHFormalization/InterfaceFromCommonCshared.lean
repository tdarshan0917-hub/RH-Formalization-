import RHFormalization.AppendixESharedPackageFunctionalCompatibility
import RHFormalization.InterfaceNonnegative

/-!
# RHFormalization.InterfaceFromCommonCshared

Appendix-E collapse: if the D-side and H-side packages are built against the
SAME shared canonical prime-power package, the full nonnegative interface
bridge follows with no further analytic input.

The only hypothesis is the package equation
`Y.B.Cshared = X.layer.overlap.Cshared`; the interface identity
`D.B = H.Bzero` then follows by transitivity through `Cshared.Bshared`,
and the threshold is `max 0 (max σ_D σ_H)`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

def buildInterfaceBridgeNonnegativeFromCommonCshared
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (h_common : Y.B.Cshared = X.layer.overlap.Cshared) :
    InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI :=
  { bridge :=
      buildInterfaceBridgeFromSharedPackageFunctionalCompatibility Y X
        { sigma :=
            max 0
              (max Y.toOperatorResolventBridge.sigma0
                X.toLegacyZeroPolePackageAPI.sigma0)
          hsigma_ge_D :=
            (le_max_left _ _).trans (le_max_right _ _)
          hsigma_ge_H :=
            (le_max_right _ _).trans (le_max_right _ _)
          h_shared_B := by
            intro s _
            rw [h_common] }
    h_sigma_nonneg := le_max_left _ _ }

#print axioms buildInterfaceBridgeNonnegativeFromCommonCshared

end

end RHFormalization
