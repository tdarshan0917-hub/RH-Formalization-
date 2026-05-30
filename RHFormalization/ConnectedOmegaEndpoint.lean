import RHFormalization.MainTheorem
import RHFormalization.OmegaConnected

/-!
# RHFormalization.ConnectedOmegaEndpoint

Endpoint wrapper after discharging the explicit `ConnectedOmegaAPI` parameter.

The global-axiom audit for `mainTheorem_from_nonnegative_interface_layer` is already
clean of project-specific global axioms.  This file removes one explicit theorem
input by using the theorem-backed connectedness package:

`defaultConnectedOmegaAPI : ConnectedOmegaAPI`.
-/

namespace RHFormalization

noncomputable section

/--
RH endpoint with the connectedness/preconnectedness of `Ω` supplied by the
theorem-backed construction in `OmegaConnected.lean`.

Compared with `mainTheorem_from_nonnegative_interface_layer`, this theorem no
longer asks the user to provide

`C : ConnectedOmegaAPI`.
-/
theorem mainTheorem_from_default_connectedOmega
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (A : MeromorphicAlgebraAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (N : LocalNormalFormObstructionAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI
      E.bridge) :
    RiemannHypothesis :=
  mainTheorem_from_nonnegative_interface_layer
    ZF Y X E defaultConnectedOmegaAPI A I N

end

end RHFormalization
