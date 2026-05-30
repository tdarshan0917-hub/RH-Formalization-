import RHFormalization.OmegaNormalFormLocalPropagationEndpoint
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# RHFormalization.OmegaMeromorphicLocalPropagationEndpoint

Narrows `OmegaNormalFormLocalPropagationAPI`.

The previous remaining input was stated only for Mathlib normal forms.  Here we
prove theorem-backed meromorphicity of `toMeromorphicNFOn f Ω`, and reduce the
remaining F-side theorem to a cleaner local propagation principle for arbitrary
meromorphic functions on Ω.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Ω-local meromorphic propagation.

This is a clean Mathlib-native local identity theorem: two meromorphic functions
on Ω that agree on a punctured neighbourhood of one point of Ω agree
codiscretely on Ω.
-/
structure OmegaMeromorphicLocalPropagationAPI where
  h_local_propagate :
    ∀ (F G : ℂ → ℂ) (z₀ : ℂ),
      z₀ ∈ Ω →
      MeromorphicOnC F Ω →
      MeromorphicOnC G Ω →
      F =ᶠ[𝓝[≠] z₀] G →
      F =ᶠ[Filter.codiscreteWithin Ω] G

/--
The Mathlib normal-form conversion of a meromorphic function is still
meromorphic on Ω.
-/
theorem toMeromorphicNFOn_meromorphicOnC_Omega
    (f : ℂ → ℂ)
    (hf : MeromorphicOnC f Ω) :
    MeromorphicOnC (toMeromorphicNFOn f Ω) Ω := by
  intro z hz
  exact
    (hf z hz).congr
      ((MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE hf hz).symm)

/--
Build the normal-form local propagation package from the cleaner meromorphic
local propagation package.
-/
def buildOmegaNormalFormLocalPropagationFromMeromorphic
    (MLP : OmegaMeromorphicLocalPropagationAPI) :
    OmegaNormalFormLocalPropagationAPI :=
  { h_local_propagate := fun f g z₀ hz hf hg hlocal =>
      MLP.h_local_propagate
        (toMeromorphicNFOn f Ω)
        (toMeromorphicNFOn g Ω)
        z₀
        hz
        (toMeromorphicNFOn_meromorphicOnC_Omega f hf)
        (toMeromorphicNFOn_meromorphicOnC_Omega g hg)
        hlocal }

/--
Endpoint after replacing normal-form local propagation by meromorphic local
propagation.
-/
theorem finalConditionalRHSpine_meromorphicLocalPropagation
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (MLP : OmegaMeromorphicLocalPropagationAPI) :
    RiemannHypothesis :=
  finalConditionalRHSpine_localNormalFormPropagation
    ZF
    Y
    X
    E
    (buildOmegaNormalFormLocalPropagationFromMeromorphic MLP)

end

end RHFormalization
