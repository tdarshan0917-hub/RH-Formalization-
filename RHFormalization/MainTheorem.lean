import RHFormalization.DFiniteStageOperator
import RHFormalization.HSideResidueArithmetic
import RHFormalization.PoleNormalForm
import RHFormalization.PoleObstructionFromNormalForm
import RHFormalization.GlobalMeromorphicIdentity
import RHFormalization.HalfPlaneGeometry
import RHFormalization.InterfaceNonnegative
import RHFormalization.FSideWrapperBuilders

/-!
# RHFormalization.MainTheorem

Final conditional theorem for the V2 Lean companion.

Iteration 9 update:
the D-side can now be supplied by a finite-stage operator legality layer, not
just by a raw detailed D export layer.
-/


namespace RHFormalization

noncomputable section

open Complex

/-- No off-critical nontrivial zeta zero can exist under the packaged D/H/E/F spine. -/
theorem no_offcritical_zero
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PoleWitnessAPI H)
    (R : RigidityNoPoleAPI D H E)
    (ρ : ℂ)
    (h_zero : IsNontrivialZetaZero ρ) :
    ρ.re ≠ (1 / 2 : ℝ) → False := by
  intro h_off
  exact
    no_ZeroWitness_of_rigidity D H E P R
      (mkZeroWitness ZF ρ h_zero h_off)

/-- RH follows from the already-assembled packaged D/H/E/F spine. -/
theorem RH_follows_from_packaged_spine
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PoleWitnessAPI H)
    (R : RigidityNoPoleAPI D H E) :
    RiemannHypothesis := by
  intro ρ h_zero
  by_contra h_off
  exact no_offcritical_zero ZF D H E P R ρ h_zero h_off

/-- Top-level companion endpoint using an already-assembled rigidity package. -/
theorem mainTheorem_of_packaged_DHEF
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PoleWitnessAPI H)
    (R : RigidityNoPoleAPI D H E) :
    RiemannHypothesis := by
  exact RH_follows_from_packaged_spine ZF D H E P R

/--
Top-level endpoint using the decomposed Appendix-F global layer.
-/
theorem mainTheorem_from_global_layer
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PoleWitnessAPI H)
    (M : MeromorphicIdentityTheoremAPI D H E)
    (A : HtotHolomorphicAPI D H)
    (N : NoPoleFromGlobalIdentityAPI D H E) :
    RiemannHypothesis := by
  exact
    RH_follows_from_packaged_spine ZF D H E P
      (buildRigidityNoPoleFromGlobalLayer D H E M A N)

/--
Endpoint using the local pole-obstruction layer.
-/
theorem mainTheorem_from_pole_obstruction_layer
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PoleWitnessAPI H)
    (M : MeromorphicIdentityTheoremAPI D H E)
    (A : HtotHolomorphicAPI D H)
    (L : LocalEqualityAtWitnessAPI D H E)
    (T : HolomorphicOnToAtAPI)
    (O : LocalPoleObstructionAPI D H E) :
    RiemannHypothesis := by
  exact
    RH_follows_from_packaged_spine ZF D H E P
      (buildRigidityNoPoleFromPoleObstructionLayer D H E M A L T O)

/--
Endpoint using the grouped H-side pole witness layer.
-/
theorem mainTheorem_from_H_grouped_pole_layer
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (G : HSidePoleWitnessLayer H)
    (M : MeromorphicIdentityTheoremAPI D H E)
    (A : HtotHolomorphicAPI D H)
    (L : LocalEqualityAtWitnessAPI D H E)
    (T : HolomorphicOnToAtAPI)
    (O : LocalPoleObstructionAPI D H E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_pole_obstruction_layer ZF D H E
      (G.toPoleWitnessAPI) M A L T O

/--
Endpoint using the H meromorphic package layer.
-/
theorem mainTheorem_from_H_meromorphic_package_layer
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (X : HMeromorphicWithGroupedPoles)
    (E : InterfaceBridgeAPI D X.toZeroPolePackageAPI)
    (M : MeromorphicIdentityTheoremAPI D X.toZeroPolePackageAPI E)
    (A : HtotHolomorphicAPI D X.toZeroPolePackageAPI)
    (L : LocalEqualityAtWitnessAPI D X.toZeroPolePackageAPI E)
    (T : HolomorphicOnToAtAPI)
    (O : LocalPoleObstructionAPI D X.toZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_H_grouped_pole_layer ZF D X.toZeroPolePackageAPI E
      X.toHSidePoleWitnessLayer M A L T O

/--
Endpoint using D export and H meromorphic package layers.
-/
theorem mainTheorem_from_D_export_and_H_meromorphic_layers
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionLayer)
    (X : HMeromorphicWithGroupedPoles)
    (E : InterfaceBridgeAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI)
    (M : MeromorphicIdentityTheoremAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E)
    (A : HtotHolomorphicAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI)
    (L : LocalEqualityAtWitnessAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E)
    (T : HolomorphicOnToAtAPI)
    (O : LocalPoleObstructionAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_H_meromorphic_package_layer ZF Y.toOperatorResolventBridge X
      E M A L T O

/--
Preferred Iteration-9 endpoint.

The D-side now starts from finite-stage operator legality, then builds the
D export layer, then the operator bridge consumed by E/F.
-/
theorem mainTheorem_from_finite_operator_and_H_meromorphic_layers
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithGroupedPoles)
    (E : InterfaceBridgeAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI)
    (M : MeromorphicIdentityTheoremAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E)
    (A : HtotHolomorphicAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI)
    (L : LocalEqualityAtWitnessAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E)
    (T : HolomorphicOnToAtAPI)
    (O : LocalPoleObstructionAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_H_meromorphic_package_layer ZF Y.toOperatorResolventBridge X
      E M A L T O

/--
Preferred Iteration-11 endpoint.

The easy F-side wrapper APIs are now built from `OmegaMathlibCompatibilityAPI`.
The remaining F-side hard input is only the local pole-obstruction theorem.
-/
theorem mainTheorem_from_wrapper_built_F_side
    (ZF : ZetaZeroFacts)
    (Ocomp : OpenOmegaAPI)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithGroupedPoles)
    (E : InterfaceBridgeAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI)
    (M : MeromorphicIdentityTheoremAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E)
    (Pobs : LocalPoleObstructionAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_finite_operator_and_H_meromorphic_layers
      ZF Y X E M
      (buildHtotHolomorphicAPIFromSummands
        Y.toOperatorResolventBridge
        X.toZeroPolePackageAPI)
      (buildLocalEqualityAtWitnessAPIFromOmega
        Ocomp
        Y.toOperatorResolventBridge
        X.toZeroPolePackageAPI
        E)
      (buildHolomorphicOnToAtAPIFromOmega Ocomp)
      Pobs

/--
Preferred Iteration-13 endpoint.

The F-side local topology now uses `defaultOpenOmegaAPI`, which is theorem-backed
by `isOpen_Omega_native`. Thus the endpoint no longer requires the user to pass
an `OpenOmegaAPI` parameter.
-/
theorem mainTheorem_from_theorem_backed_Omega
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithGroupedPoles)
    (E : InterfaceBridgeAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI)
    (M : MeromorphicIdentityTheoremAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E)
    (Pobs : LocalPoleObstructionAPI Y.toOperatorResolventBridge X.toZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_wrapper_built_F_side
      ZF
      defaultOpenOmegaAPI
      Y X E M Pobs

/--
Preferred Iteration-14 endpoint.

The H-side grouped residue positivity/nonzero arithmetic is now built by
`HSideResidueArithmetic.lean`; the endpoint no longer requires prepackaged
`GroupedMultiplicityPositiveAPI` or `GroupedResidueNonzeroAPI`.
-/
theorem mainTheorem_from_H_residue_arithmetic_layer
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithArithmeticGroupedPoles)
    (E :
      InterfaceBridgeAPI
        Y.toOperatorResolventBridge
        X.toHMeromorphicWithGroupedPoles.toZeroPolePackageAPI)
    (M :
      MeromorphicIdentityTheoremAPI
        Y.toOperatorResolventBridge
        X.toHMeromorphicWithGroupedPoles.toZeroPolePackageAPI
        E)
    (Pobs :
      LocalPoleObstructionAPI
        Y.toOperatorResolventBridge
        X.toHMeromorphicWithGroupedPoles.toZeroPolePackageAPI
        E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_theorem_backed_Omega
      ZF
      Y
      X.toHMeromorphicWithGroupedPoles
      E
      M
      Pobs

/--
Preferred Iteration-15 endpoint.

The H-side genuine-pole conversion is now supplied by an explicit local
pole-normal-form layer, rather than by a raw `PrincipalPartImpliesGenuinePoleAPI`.
-/
theorem mainTheorem_from_pole_normal_form_layer
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E :
      InterfaceBridgeAPI
        Y.toOperatorResolventBridge
        X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles.toZeroPolePackageAPI)
    (M :
      MeromorphicIdentityTheoremAPI
        Y.toOperatorResolventBridge
        X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles.toZeroPolePackageAPI
        E)
    (Pobs :
      LocalPoleObstructionAPI
        Y.toOperatorResolventBridge
        X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles.toZeroPolePackageAPI
        E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_H_residue_arithmetic_layer
      ZF
      Y
      X.toArithmeticGroupedPoles
      E
      M
      Pobs

/--
Preferred Iteration-16 endpoint.

The local pole obstruction is now built from a narrower
`LocalNormalFormObstructionAPI`, using the H-side normal-form package.
-/
theorem mainTheorem_from_local_normal_form_obstruction
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI)
    (M : MeromorphicIdentityTheoremAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI E)
    (O : LocalNormalFormObstructionAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_theorem_backed_Omega
      ZF
      Y
      X.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles
      E
      M
      (buildLocalPoleObstructionFromHNormalFormPackage
        Y.toOperatorResolventBridge
        X
        E
        O)

/--
Preferred Iteration-17 endpoint.

The global Appendix-F identity is now supplied by decomposed meromorphic identity
components: connectedness of `Ω`, overlap geometry, meromorphicity of both sides,
and the meromorphic identity principle.
-/
theorem mainTheorem_from_global_meromorphic_identity_components
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI)
    (C : ConnectedOmegaAPI)
    (O : OverlapGeometryAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI E)
    (A : MeromorphicAlgebraAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (N : LocalNormalFormObstructionAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_local_normal_form_obstruction
      ZF
      Y
      X
      E
      (buildMeromorphicIdentityTheoremAPIFromGeometryAndAlgebra
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI
        E
        C
        O
        A
        I)
      N

/--
Preferred Iteration-18 endpoint.

The overlap geometry is now theorem-backed from right-half-plane geometry.
The user supplies only the nonnegativity of the interface threshold `E.sigma`.
-/
theorem mainTheorem_from_theorem_backed_overlap_geometry
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI)
    (hσ : 0 ≤ E.sigma)
    (C : ConnectedOmegaAPI)
    (A : MeromorphicAlgebraAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (N : LocalNormalFormObstructionAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI E) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_global_meromorphic_identity_components
      ZF
      Y
      X
      E
      C
      (defaultOverlapGeometryAPI
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI
        E
        hσ)
      A
      I
      N

/--
Preferred Iteration-19 endpoint.

The Appendix-E interface now carries its nonnegative half-plane threshold internally.
Thus the endpoint no longer has a loose parameter `hσ : 0 ≤ E.sigma`.
-/
theorem mainTheorem_from_nonnegative_interface_layer
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI)
    (C : ConnectedOmegaAPI)
    (A : MeromorphicAlgebraAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (N :
      LocalNormalFormObstructionAPI
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI
        E.bridge) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_theorem_backed_overlap_geometry
      ZF
      Y
      X
      E.bridge
      E.h_sigma_nonneg
      C
      A
      I
      N

end

end RHFormalization
