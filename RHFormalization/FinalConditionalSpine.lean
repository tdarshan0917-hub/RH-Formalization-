import RHFormalization.InterfaceBridgeNonnegativeFromPlain

/-!
# RHFormalization.FinalConditionalSpine

Canonical current endpoint.

This is the clean conditional RH spine after:
* removing project-specific global axioms;
* discharging topology/meromorphic algebra/local pole obstruction support layers;
* replacing the old pointwise meromorphic identity API with a Mathlib-native
  normal-form/codiscrete propagation package;
* removing the auxiliary nonnegative-interface wrapper.

Remaining explicit inputs are exactly:
* `ZF`   : zeta-zero nonreal/off-cut fact;
* `Y`    : Appendix-D operator-side construction/export;
* `X`    : Appendix-H zero-side meromorphic pole package;
* `E`    : Appendix-E bridge identity;
* `ONFP` : Appendix-F normal-form codiscrete propagation.
-/

namespace RHFormalization

noncomputable section

/--
Final current conditional RH theorem.

This is not an unconditional Lean proof of RH. It is the current axiom-clean
conditional spine whose remaining inputs are the serious D/H/E/F proof packages
plus the zeta-zero fact.
-/
theorem finalConditionalRHSpine
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (ONFP : OmegaNormalFormCodiscretePropagationAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormPropagation_plainInterface
    ZF Y X E ONFP

end

end RHFormalization
