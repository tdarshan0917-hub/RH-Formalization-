import RHFormalization.MainTheorem
import RHFormalization.DefaultZetaZeroFacts
import RHFormalization.DefaultMeromorphicAlgebraAPI

/-!
# RHFormalization.MainTheoremFromRealZeroFreeDefaultA

Iteration endpoint with:
* `ZF : ZetaZeroFacts` replaced by the explicit real-zero-free zeta hypothesis;
* `A : MeromorphicAlgebraAPI` supplied by `defaultMeromorphicAlgebraAPI`.

Remaining frontier:
`Y`, `X`, `E`, `C`, `I`, and `N`.
-/

namespace RHFormalization

noncomputable section

open Complex

theorem mainTheorem_from_realZeroFree_nonnegative_interface_defaultA
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E :
      InterfaceBridgeNonnegativeAPI
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI)
    (C : ConnectedOmegaAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (N :
      LocalNormalFormObstructionAPI
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI
        E.bridge) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_nonnegative_interface_layer
      (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
      Y
      X
      E
      C
      defaultMeromorphicAlgebraAPI
      I
      N

#print axioms mainTheorem_from_realZeroFree_nonnegative_interface_defaultA

end

end RHFormalization
