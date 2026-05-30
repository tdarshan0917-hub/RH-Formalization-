import RHFormalization.PuncturedMeromorphicIdentityEndpoint

/-!
# RHFormalization.OmegaPuncturedIdentityEndpoint

Ω-specific punctured meromorphic identity endpoint.

The previous endpoint used a generic punctured identity principle over arbitrary
sets `U`.  The RH spine only needs this principle on the slit plane `Ω`.

This file narrows

`IP : PuncturedMeromorphicIdentityAPI`

to

`OIP : OmegaPuncturedMeromorphicIdentityAPI`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter Bornology

/--
Ω-specific punctured meromorphic identity principle.

This is the exact form used by the RH closure: meromorphic functions on `Ω` that
agree on the nonempty overlap give punctured-neighbourhood equality at any point
of `Ω`.
-/
structure OmegaPuncturedMeromorphicIdentityAPI where
  h_punctured_identity :
    ∀ (f g : ℂ → ℂ) (V : Set ℂ) (z : ℂ),
      IsOpen V →
      V.Nonempty →
      V ⊆ Ω →
      z ∈ Ω →
      MeromorphicOnC f Ω →
      MeromorphicOnC g Ω →
      Set.EqOn f g V →
      PuncturedEqAtC f g z

/--
Endpoint using the Ω-specific punctured identity principle.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_puncturedIdentity`,
this theorem no longer requires the generic

`IP : PuncturedMeromorphicIdentityAPI`.

It only requires the Ω-specific identity package.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_omegaPuncturedIdentity
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (OIP : OmegaPuncturedMeromorphicIdentityAPI) :
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
      OIP.h_punctured_identity
        D.FH
        (fun s => Htot D H s - H.Zpole s)
        (InterfaceOverlap Eb)
        W.s0
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
