import RHFormalization.AppendixELocalBridgeCore

namespace RHFormalization

noncomputable section

open Complex Topology Filter

-- Exact remaining Appendix-E shared-package target.
example
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (sigma : ℝ)
    (hsigma_ge_D : Y.toOperatorResolventBridge.sigma0 ≤ sigma)
    (hsigma_ge_H : X.toLegacyZeroPolePackageAPI.sigma0 ≤ sigma)
    (h_shared :
      ∀ s : ℂ, s ∈ RightHalfPlane sigma →
        Y.toOperatorResolventBridge.B s =
          X.toLegacyZeroPolePackageAPI.Bzero s) :
    InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI :=
  { sigma := sigma
    hsigma_ge_D := hsigma_ge_D
    hsigma_ge_H := hsigma_ge_H
    h_interface := h_shared }

#check DDetailedConstructionWithOperatorLegality.toOperatorResolventBridge
#check HMeromorphicWithNormalFormPoles.toLegacyZeroPolePackageAPI
#print InterfaceBridgeAPI

end

end RHFormalization
