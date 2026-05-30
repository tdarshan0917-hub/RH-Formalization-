import RHFormalization.DefaultOmegaPreperfect
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# RHFormalization.OmegaCodiscreteIdentityFromNormalForms

Narrows `OmegaCodiscreteMeromorphicIdentityAPI`.

Mathlib gives:

`toMeromorphicNFOn_eqOn_codiscrete`

so any meromorphic function is codiscretely equal to its meromorphic normal form.
Thus, to prove codiscrete equality of two meromorphic functions, it suffices to prove
codiscrete equality of their Mathlib normal forms.

This file replaces:

`OCI : OmegaCodiscreteMeromorphicIdentityAPI`

by the narrower normal-form identity input:

`ONFI : OmegaNormalFormCodiscreteIdentityAPI`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Ω-specific meromorphic normal-form codiscrete identity principle.

This is narrower than `OmegaCodiscreteMeromorphicIdentityAPI`: it only asks for
codiscrete equality of the Mathlib meromorphic normal forms.
-/
structure OmegaNormalFormCodiscreteIdentityAPI where
  h_nf_codiscrete_identity :
    ∀ (f g : ℂ → ℂ) (V : Set ℂ),
      IsOpen V →
      V.Nonempty →
      V ⊆ Ω →
      MeromorphicOnC f Ω →
      MeromorphicOnC g Ω →
      Set.EqOn f g V →
      toMeromorphicNFOn f Ω =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn g Ω

/--
Build the Ω-codiscrete meromorphic identity package from normal-form codiscrete
identity.

The only Mathlib facts used here are that a meromorphic function is codiscretely
equal to its normal form.
-/
def buildOmegaCodiscreteIdentityFromNormalForms
    (ONFI : OmegaNormalFormCodiscreteIdentityAPI) :
    OmegaCodiscreteMeromorphicIdentityAPI :=
  { h_codiscrete_identity := fun f g V hVopen hVnonempty hVsubset hf hg hEq =>
      by
        have hf_to_nf :
            f =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn f Ω :=
          toMeromorphicNFOn_eqOn_codiscrete hf

        have hnf :
            toMeromorphicNFOn f Ω =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn g Ω :=
          ONFI.h_nf_codiscrete_identity
            f g V hVopen hVnonempty hVsubset hf hg hEq

        have hg_to_nf :
            g =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn g Ω :=
          toMeromorphicNFOn_eqOn_codiscrete hg

        exact hf_to_nf.trans (hnf.trans hg_to_nf.symm) }

/--
Endpoint after replacing `OmegaCodiscreteMeromorphicIdentityAPI` by normal-form
codiscrete identity.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormCodiscreteIdentity
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (ONFI : OmegaNormalFormCodiscreteIdentityAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_codiscreteIdentity_preperfect
    ZF
    Y
    X
    E
    (buildOmegaCodiscreteIdentityFromNormalForms ONFI)

end

end RHFormalization
