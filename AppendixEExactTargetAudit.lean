import RHFormalization.AppendixELocalBridgeCore

namespace RHFormalization

noncomputable section

open Complex Topology Filter

#check buildInterfaceBridgeFromLocalComparison

-- This is the exact remaining Appendix-E local comparison theorem shape.
example
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (sigma : ℝ)
    (hsigma_ge_D : Y.toOperatorResolventBridge.sigma0 ≤ sigma)
    (hsigma_ge_H : X.toLegacyZeroPolePackageAPI.sigma0 ≤ sigma)
    (h_local :
      ∀ s : ℂ, s ∈ RightHalfPlane sigma →
        Y.toOperatorResolventBridge.FH s =
          Htot
            Y.toOperatorResolventBridge
            X.toLegacyZeroPolePackageAPI s
            - X.toLegacyZeroPolePackageAPI.Zpole s) :
    InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI :=
  buildInterfaceBridgeFromLocalComparison
    Y.toOperatorResolventBridge
    X.toLegacyZeroPolePackageAPI
    sigma
    hsigma_ge_D
    hsigma_ge_H
    h_local

end

end RHFormalization
