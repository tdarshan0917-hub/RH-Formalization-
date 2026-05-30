import RHFormalization.OmegaMeromorphicZeroPropagationEndpoint

/-!
# RHFormalization.FinalZeroPropagationSpine

Canonical strongest conditional endpoint after all current cleanup and narrowing.

Remaining explicit inputs:
* `ZF` : zeta-zero nonreal/off-cut fact;
* `Y`  : Appendix-D operator-side construction/export;
* `X`  : Appendix-H zero-side meromorphic pole package;
* `E`  : Appendix-E bridge identity;
* `ZP` : Appendix-F meromorphic zero-propagation theorem on Ω.
-/

namespace RHFormalization

noncomputable section

/--
Current strongest conditional RH spine.

This is not an unconditional Lean proof of RH. It is the axiom-clean conditional
spine whose remaining inputs are exactly the serious D/H/E/F packages plus the
zeta-zero fact.
-/
theorem finalZeroPropagationRHSpine
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (ZP : OmegaMeromorphicZeroPropagationAPI) :
    RiemannHypothesis :=
  finalConditionalRHSpine_meromorphicZeroPropagation
    ZF Y X E ZP

end

end RHFormalization
