import RHFormalization.MainTheoremFromRealZeroFreeDefaultA
import RHFormalization.DefaultConnectedOmegaAPI

/-!
# RHFormalization.MainTheoremFromRealZeroFreeDefaultAC

Endpoint with:
* `ZF` reduced to the explicit real-zero-free zeta hypothesis;
* `A : MeromorphicAlgebraAPI` supplied by `defaultMeromorphicAlgebraAPI`;
* `C : ConnectedOmegaAPI` supplied by `defaultConnectedOmegaAPI`.

Remaining frontier:
`Y`, `X`, `E`, `I`, and `N`, plus the real-zero-free zeta fact.
-/

namespace RHFormalization

noncomputable section

open Complex

theorem mainTheorem_from_realZeroFree_nonnegative_interface_defaultAC
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E :
      InterfaceBridgeNonnegativeAPI
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (N :
      LocalNormalFormObstructionAPI
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI
        E.bridge) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_realZeroFree_nonnegative_interface_defaultA
      h_real_zero_free
      Y
      X
      E
      defaultConnectedOmegaAPI
      I
      N

#print axioms mainTheorem_from_realZeroFree_nonnegative_interface_defaultAC

end

end RHFormalization
