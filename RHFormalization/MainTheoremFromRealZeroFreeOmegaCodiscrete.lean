import RHFormalization.MainTheoremFromRealZeroFreeOmegaPunctured
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete

/-!
# RHFormalization.MainTheoremFromRealZeroFreeOmegaCodiscrete

Endpoint with:
* `ZF : ZetaZeroFacts` reduced to the explicit real-zero-free zeta hypothesis;
* broad pointwise meromorphic identity removed;
* Ω-specific punctured identity reduced to codiscrete identity plus preperfectness.

Remaining frontier:
`h_real_zero_free`, `Y`, `X`, `E`, `OCI`, and `OPP`.
-/

namespace RHFormalization

noncomputable section

open Complex

theorem mainTheorem_from_realZeroFree_omegaCodiscreteIdentity
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E :
      InterfaceBridgeNonnegativeAPI
        Y.toOperatorResolventBridge
        X.toLegacyZeroPolePackageAPI)
    (OCI : OmegaCodiscreteMeromorphicIdentityAPI)
    (OPP : OmegaPreperfectAPI) :
    RiemannHypothesis := by
  exact
    mainTheorem_from_realZeroFree_omegaPuncturedIdentity
      h_real_zero_free
      Y
      X
      E
      (buildOmegaPuncturedIdentityFromCodiscrete OCI OPP)

#print axioms mainTheorem_from_realZeroFree_omegaCodiscreteIdentity

end

end RHFormalization
