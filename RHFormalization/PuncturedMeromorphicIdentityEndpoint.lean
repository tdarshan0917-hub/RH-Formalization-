import RHFormalization.PuncturedIdentityLocalCore
import RHFormalization.DefaultDenominatorSimpleZeroOrder
import RHFormalization.MainTheorem

/-!
# RHFormalization.PuncturedMeromorphicIdentityEndpoint

Endpoint using the punctured meromorphic identity principle.

This replaces the old pointwise global meromorphic identity input

`I : MeromorphicIdentityPrincipleAPI`

by the Mathlib-compatible punctured identity input

`IP : PuncturedMeromorphicIdentityAPI`.

The local pole contradiction only needs punctured equality near the witness pole,
not pointwise equality on all of `Ω`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter Bornology

/--
Build the default principal-part negative-order package from the theorem-backed
local chain already developed.
-/
def defaultPrincipalPartNegativeOrderAPI :
    PrincipalPartNegativeOrderAPI :=
  buildPrincipalPartNegativeOrderAPIFromCobounded
    defaultPrincipalPartMeromorphicAtAPI
    (buildPrincipalPartCoboundedAPIFromModel
      (buildSimplePolePlusHolomorphicCoboundedAPIFromSplit
        (buildSimplePoleCoboundedAPIFromNegativeOrder
          (buildSimplePoleNegativeOrderAPIFromDenominator
            defaultDenominatorSimpleZeroOrderAPI))
        defaultCoboundedAddFiniteLimitAPI))

/--
Punctured-identity endpoint.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_localPoleClosed`,
this theorem no longer requires the old pointwise

`I : MeromorphicIdentityPrincipleAPI`.

Instead, it requires the punctured meromorphic identity principle

`IP : PuncturedMeromorphicIdentityAPI`.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_puncturedIdentity
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (IP : PuncturedMeromorphicIdentityAPI) :
    RiemannHypothesis := by
  intro ρ hρ
  by_contra h_off

  let D : OperatorResolventBridge :=
    Y.toOperatorResolventBridge

  let H : ZeroPolePackageAPI :=
    X.toLegacyZeroPolePackageAPI

  let Eb : InterfaceBridgeAPI D H :=
    E.bridge

  let W : ZeroWitness :=
    mkZeroWitness ZF ρ hρ h_off

  have hpunct :
      PuncturedEqAtC
        D.FH
        (fun s => Htot D H s - H.Zpole s)
        W.s0 := by
    exact
      IP.h_punctured_identity
        D.FH
        (fun s => Htot D H s - H.Zpole s)
        Ω
        (InterfaceOverlap Eb)
        W.s0
        defaultConnectedOmegaAPI.h_preconnected_Omega
        (defaultOverlapGeometryAPI D H Eb E.h_sigma_nonneg).h_overlap_open
        (defaultOverlapGeometryAPI D H Eb E.h_sigma_nonneg).h_overlap_nonempty
        (defaultOverlapGeometryAPI D H Eb E.h_sigma_nonneg).h_overlap_subset_Omega
        W.hs0_in_Omega
        (buildComparisonMeromorphicAPI D H defaultMeromorphicAlgebraAPI).h_left_meromorphic
        (buildComparisonMeromorphicAPI D H defaultMeromorphicAlgebraAPI).h_right_meromorphic
        (local_split_eqOn D H Eb)

  have hFH_at :
      HolomorphicAtC D.FH W.s0 :=
    HolomorphicOnC.holomorphicAt
      defaultOpenOmegaAPI
      D.hFH_holo
      W.hs0_in_Omega

  have hHtot_at :
      HolomorphicAtC (Htot D H) W.s0 :=
    HolomorphicOnC.holomorphicAt
      defaultOpenOmegaAPI
      (buildHtotHolomorphicAPIFromSummands D H).h_Htot_holo
      W.hs0_in_Omega

  have h_genuine :
      HasGenuinePole H.Zpole W.s0 := by
    change
      HasGenuinePole X.toLegacyZeroPolePackageAPI.Zpole W.s0
    exact
      ((X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles.toHSidePoleWitnessLayer).toPoleWitnessAPI).h_genuine_pole W

  let G :
      GenuinePoleNormalForm H.Zpole W.s0 :=
    (X.toLegacyGenuinePoleNormalFormAPI).h_normal_form W h_genuine

  have h_principal :
      PrincipalPartNormalForm H.Zpole W.s0 G.principalCoeff :=
    principalPartNormalFormOfGenuine
      X.toPoleNormalFormLayer
      G

  have hZneg :
      meromorphicOrderAt H.Zpole W.s0 < 0 :=
    defaultPrincipalPartNegativeOrderAPI.h_negative_order
      H.Zpole
      W.s0
      G.principalCoeff
      h_principal

  exact
    local_order_obstruction_from_punctured_holomorphic_balance
      D.FH
      (Htot D H)
      H.Zpole
      W.s0
      hpunct
      hFH_at
      hHtot_at
      hZneg

end

end RHFormalization
