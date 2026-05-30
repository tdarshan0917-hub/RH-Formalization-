import RHFormalization.OmegaCodiscreteIdentityFromNormalForms
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# RHFormalization.OmegaNormalFormPropagationEndpoint

Narrows `OmegaNormalFormCodiscreteIdentityAPI`.

We prove the local codiscrete normal-form agreement on the overlap from:

* `Set.EqOn f g V`;
* `V ⊆ Ω`;
* Mathlib's `toMeromorphicNFOn_eqOn_codiscrete`;
* `Filter.codiscreteWithin_mono`.

The remaining identity-side input is now only the propagation of normal-form
codiscrete equality from the overlap to all of Ω.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Normal-form codiscrete propagation on Ω.

This is the remaining identity-theorem burden after the local overlap-to-normal-form
part is discharged.
-/
structure OmegaNormalFormCodiscretePropagationAPI where
  h_nf_propagate :
    ∀ (f g : ℂ → ℂ) (V : Set ℂ),
      IsOpen V →
      V.Nonempty →
      V ⊆ Ω →
      MeromorphicOnC f Ω →
      MeromorphicOnC g Ω →
      toMeromorphicNFOn f Ω =ᶠ[Filter.codiscreteWithin V] toMeromorphicNFOn g Ω →
      toMeromorphicNFOn f Ω =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn g Ω

/--
On the overlap `V`, pointwise equality of meromorphic functions gives codiscrete
equality of their Ω-normal forms.

This part is theorem-backed from Mathlib.
-/
theorem omega_normalForms_codiscrete_on_overlap
    (f g : ℂ → ℂ)
    (V : Set ℂ)
    (hVsubset : V ⊆ Ω)
    (hf : MeromorphicOnC f Ω)
    (hg : MeromorphicOnC g Ω)
    (hEq : Set.EqOn f g V) :
    toMeromorphicNFOn f Ω =ᶠ[Filter.codiscreteWithin V] toMeromorphicNFOn g Ω := by
  have hVle :
      Filter.codiscreteWithin V ≤ Filter.codiscreteWithin Ω :=
    Filter.codiscreteWithin_mono hVsubset

  have hf_to_nf_Ω :
      f =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn f Ω :=
    toMeromorphicNFOn_eqOn_codiscrete hf

  have hg_to_nf_Ω :
      g =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn g Ω :=
    toMeromorphicNFOn_eqOn_codiscrete hg

  have hf_to_nf_V :
      f =ᶠ[Filter.codiscreteWithin V] toMeromorphicNFOn f Ω :=
    hf_to_nf_Ω.filter_mono hVle

  have hg_to_nf_V :
      g =ᶠ[Filter.codiscreteWithin V] toMeromorphicNFOn g Ω :=
    hg_to_nf_Ω.filter_mono hVle

  have hfg_V :
      f =ᶠ[Filter.codiscreteWithin V] g := by
    filter_upwards [Filter.self_mem_codiscreteWithin V] with z hz
    exact hEq hz

  exact hf_to_nf_V.symm.trans (hfg_V.trans hg_to_nf_V)

/--
Build the previous normal-form codiscrete identity API from the propagation-only API.
-/
def buildOmegaNormalFormCodiscreteIdentityFromPropagation
    (ONFP : OmegaNormalFormCodiscretePropagationAPI) :
    OmegaNormalFormCodiscreteIdentityAPI :=
  { h_nf_codiscrete_identity := fun f g V hVopen hVnonempty hVsubset hf hg hEq =>
      ONFP.h_nf_propagate
        f
        g
        V
        hVopen
        hVnonempty
        hVsubset
        hf
        hg
        (omega_normalForms_codiscrete_on_overlap
          f g V hVsubset hf hg hEq) }

/--
Endpoint after replacing `OmegaNormalFormCodiscreteIdentityAPI` by the propagation-only
normal-form identity package.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormPropagation
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (ONFP : OmegaNormalFormCodiscretePropagationAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_normalFormCodiscreteIdentity
    ZF
    Y
    X
    E
    (buildOmegaNormalFormCodiscreteIdentityFromPropagation ONFP)

end

end RHFormalization
