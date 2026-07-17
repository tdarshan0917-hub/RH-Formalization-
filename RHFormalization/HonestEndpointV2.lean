import RHFormalization.OmegaPuncturedIdentityEndpoint
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
import RHFormalization.DefaultOmegaCodiscreteIdentity
import RHFormalization.DefaultOmegaPreperfect

/-!
# HONEST ENDPOINT V2 — content inputs only, living identity route

Generalizes the proven `mainTheorem_from_default_connectedOmega_meromorphicAlgebra_
codiscreteIdentity` from the full `Y : DDetailedConstructionWithOperatorLegality`
to the bare Appendix-D export `D : OperatorResolventBridge` (the manuscript's
actual D-side interface), and derives the Ω-punctured identity package from the
two PROVEN defaults (codiscrete identity + Ω preperfect). No bitrotted principle,
no designed witnesses, no M/O hypotheses.

Content inputs (the manuscript's burden, nothing else):
* ZF — zeta zero facts
* D  — Appendix D export: FH, RH ∈ O(Ω), FH = B + RH on ℜs > D.σ₀
* X  — Appendix H package with pole normal form (Zpole ∈ Mer(Ω), Harch ∈ O(Ω),
       half-plane split, grouped principal parts at witness points)
* E  — Appendix E overlap bridge with σ ≥ 0

FIREWALL: no hypothesis may assert regularity of raw Bshared outside its
convergence half-plane. (See HonestEndpoint.lean.)
-/

namespace RHFormalization
noncomputable section
open Complex Set

theorem RH_from_manuscript_content
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI D X.toLegacyZeroPolePackageAPI) :
    RiemannHypothesis := by
  intro ρ hρ
  by_contra h_off
  let H : ZeroPolePackageAPI := X.toLegacyZeroPolePackageAPI
  let Eb : InterfaceBridgeAPI D H := E.bridge
  let W : ZeroWitness := mkZeroWitness ZF ρ hρ h_off
  let OIP : OmegaPuncturedMeromorphicIdentityAPI :=
    buildOmegaPuncturedIdentityFromCodiscrete
      defaultOmegaCodiscreteIdentityAPI
      defaultOmegaPreperfectAPI
  have hpunct :
      PuncturedEqAtC D.FH (fun s => Htot D H s - H.Zpole s) W.s0 := by
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
  have hFH_at : HolomorphicAtC D.FH W.s0 :=
    HolomorphicOnC.holomorphicAt defaultOpenOmegaAPI D.hFH_holo W.hs0_in_Omega
  have hHtot_at : HolomorphicAtC (Htot D H) W.s0 :=
    HolomorphicOnC.holomorphicAt defaultOpenOmegaAPI
      (buildHtotHolomorphicAPIFromSummands D H).h_Htot_holo W.hs0_in_Omega
  have h_genuine : HasGenuinePole H.Zpole W.s0 := by
    change HasGenuinePole X.toLegacyZeroPolePackageAPI.Zpole W.s0
    exact
      ((X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles.toHSidePoleWitnessLayer).toPoleWitnessAPI).h_genuine_pole W
  let G : GenuinePoleNormalForm H.Zpole W.s0 :=
    (X.toLegacyGenuinePoleNormalFormAPI).h_normal_form W h_genuine
  have h_principal :
      PrincipalPartNormalForm H.Zpole W.s0 G.principalCoeff :=
    principalPartNormalFormOfGenuine X.toPoleNormalFormLayer G
  have hZneg : meromorphicOrderAt H.Zpole W.s0 < 0 :=
    defaultPrincipalPartNegativeOrderAPI.h_negative_order
      H.Zpole W.s0 G.principalCoeff h_principal
  exact
    local_order_obstruction_from_punctured_holomorphic_balance
      D.FH (Htot D H) H.Zpole W.s0 hpunct hFH_at hHtot_at hZneg

#check @RH_from_manuscript_content
#print axioms RH_from_manuscript_content

end
end RHFormalization
