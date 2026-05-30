import RHFormalization.OmegaNormalFormPropagationEndpoint

/-!
# RHFormalization.InterfaceBridgeNonnegativeFromPlain

Removes the explicit nonnegativity wrapper from the interface bridge input.

Given an arbitrary `InterfaceBridgeAPI D H`, replace its threshold `sigma` by
`max sigma 0`.  The right half-plane becomes smaller, so the interface identity
continues to hold there, and the new threshold is nonnegative.

This does not discharge Appendix E itself; it only removes the auxiliary
nonnegativity condition from the endpoint.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
If `σ ≤ τ`, then the right half-plane with threshold `τ` is contained in the
right half-plane with threshold `σ`.
-/
theorem RightHalfPlane_subset_of_le
    {σ τ : ℝ}
    (hστ : σ ≤ τ) :
    RightHalfPlane τ ⊆ RightHalfPlane σ := by
  intro s hs
  dsimp [RightHalfPlane] at hs ⊢
  exact lt_of_le_of_lt hστ hs

/--
Upgrade an arbitrary interface bridge to a nonnegative-threshold interface bridge
by replacing the threshold with `max sigma 0`.
-/
def buildInterfaceBridgeNonnegativeFromPlain
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) :
    InterfaceBridgeNonnegativeAPI D H :=
  { bridge :=
      { sigma := max E.sigma 0
        hsigma_ge_D :=
          le_trans E.hsigma_ge_D (le_max_left E.sigma 0)
        hsigma_ge_H :=
          le_trans E.hsigma_ge_H (le_max_left E.sigma 0)
        h_interface := by
          intro s hs
          exact
            E.h_interface s
              (RightHalfPlane_subset_of_le
                (le_max_left E.sigma 0)
                hs) }
    h_sigma_nonneg :=
      le_max_right E.sigma 0 }

/--
Endpoint after removing the explicit nonnegativity wrapper from the interface input.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormPropagation`,
this theorem asks only for

`E : InterfaceBridgeAPI ...`

rather than

`E : InterfaceBridgeNonnegativeAPI ...`.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormPropagation_plainInterface
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (ONFP : OmegaNormalFormCodiscretePropagationAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormPropagation
    ZF
    Y
    X
    (buildInterfaceBridgeNonnegativeFromPlain
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI
      E)
    ONFP

end

end RHFormalization
