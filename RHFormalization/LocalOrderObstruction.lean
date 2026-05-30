import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.ConnectedOmegaMeromorphicAlgebraEndpoint

/-!
# RHFormalization.LocalOrderObstruction

Order-theoretic local pole obstruction.

This narrows the local Appendix-F pole obstruction.  Instead of carrying the full
`LocalNormalFormObstructionAPI`, we prove the holomorphic-balance contradiction
from Mathlib's meromorphic-order machinery.

The remaining local input is that a principal-part normal form has negative
meromorphic order.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
If `F = G - Z` locally near `z`, and `F` and `G` are holomorphic at `z`, then
`Z` cannot have negative meromorphic order at `z`.
-/
theorem local_order_obstruction_from_holomorphic_balance
    (F G Z : ℂ → ℂ)
    (z : ℂ)
    (hlocal : LocalEqAtC F (fun s => G s - Z s) z)
    (hF : HolomorphicAtC F z)
    (hG : HolomorphicAtC G z)
    (hZneg : meromorphicOrderAt Z z < 0) :
    False := by
  have hZeq_nhds :
      Z =ᶠ[𝓝 z] (fun s => G s - F s) := by
    filter_upwards [hlocal] with w hw
    have hcalc : Z w = G w - F w := by
      rw [hw]
      ring
    exact hcalc

  have hZeq_punct :
      Z =ᶠ[𝓝[≠] z] (fun s => G s - F s) := by
    exact (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z) hZeq_nhds

  have hdiff_holo :
      HolomorphicAtC (fun s => G s - F s) z :=
    hG.sub hF

  have hdiff_nonneg :
      0 ≤ meromorphicOrderAt (fun s => G s - F s) z :=
    hdiff_holo.meromorphicOrderAt_nonneg

  have horder_eq :
      meromorphicOrderAt Z z =
        meromorphicOrderAt (fun s => G s - F s) z := by
    exact meromorphicOrderAt_congr hZeq_punct

  have hZneg_diff :
      meromorphicOrderAt (fun s => G s - F s) z < 0 := by
    simpa [horder_eq] using hZneg

  exact not_lt_of_ge hdiff_nonneg hZneg_diff

/--
Remaining narrow local input: a principal-part normal form has negative
meromorphic order.
-/
structure PrincipalPartNegativeOrderAPI where
  h_negative_order :
    ∀ (f : ℂ → ℂ) (s0 coeff : ℂ),
      PrincipalPartNormalForm f s0 coeff →
        meromorphicOrderAt f s0 < 0

/--
Build the previous `LocalNormalFormObstructionAPI` from the narrow
principal-part-negative-order API and the theorem-backed local order obstruction.
-/
def buildLocalNormalFormObstructionFromOrder
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PrincipalPartNegativeOrderAPI) :
    LocalNormalFormObstructionAPI D H E :=
  { h_no_normal_form := fun W coeff hlocal hFH hHtot hpp =>
      local_order_obstruction_from_holomorphic_balance
        D.FH
        (Htot D H)
        H.Zpole
        W.s0
        hlocal
        hFH
        hHtot
        (P.h_negative_order H.Zpole W.s0 coeff hpp) }

/--
Endpoint after replacing the broad `LocalNormalFormObstructionAPI` input by the
narrower `PrincipalPartNegativeOrderAPI`.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_orderObstruction
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (P : PrincipalPartNegativeOrderAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_and_meromorphicAlgebra
    ZF
    Y
    X
    E
    I
    (buildLocalNormalFormObstructionFromOrder
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI
      E.bridge
      P)

end

end RHFormalization
