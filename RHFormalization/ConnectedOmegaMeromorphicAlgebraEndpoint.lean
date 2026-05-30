import RHFormalization.ConnectedOmegaEndpoint
import RHFormalization.DefaultMeromorphicAlgebra

/-!
# RHFormalization.ConnectedOmegaMeromorphicAlgebraEndpoint

Endpoint wrapper after discharging both:

* `ConnectedOmegaAPI`;
* `MeromorphicAlgebraAPI`.
-/

namespace RHFormalization

noncomputable section

/--
RH endpoint with both the connectedness of `Ω` and the meromorphic algebra package
supplied by theorem-backed defaults.
-/
theorem mainTheorem_from_default_connectedOmega_and_meromorphicAlgebra
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (N : LocalNormalFormObstructionAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI
      E.bridge) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega
    ZF Y X E defaultMeromorphicAlgebraAPI I N

end

end RHFormalization
