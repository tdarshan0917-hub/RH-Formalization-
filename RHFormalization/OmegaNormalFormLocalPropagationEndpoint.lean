import RHFormalization.FinalConditionalSpine
import RHFormalization.ONFPLocalFrequent
import RHFormalization.OmegaNormalFormPropagationEndpoint

/-!
# RHFormalization.OmegaNormalFormLocalPropagationEndpoint

Narrows the remaining `OmegaNormalFormCodiscretePropagationAPI`.

The theorem-backed helper `eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_of_mem_open`
already proves:

codiscrete equality on an open overlap `V`
  ⇒ punctured-neighbourhood equality at any point `z₀ ∈ V`.

Therefore the remaining Appendix-F propagation burden can be stated locally:

punctured equality of normal forms at one point of Ω
  ⇒ codiscrete equality of normal forms on all of Ω.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Local-to-global normal-form propagation on Ω.

This is the remaining Appendix-F propagation theorem after the overlap-to-local
codiscrete step has been discharged.
-/
structure OmegaNormalFormLocalPropagationAPI where
  h_local_propagate :
    ∀ (f g : ℂ → ℂ) (z₀ : ℂ),
      z₀ ∈ Ω →
      MeromorphicOnC f Ω →
      MeromorphicOnC g Ω →
      toMeromorphicNFOn f Ω =ᶠ[𝓝[≠] z₀] toMeromorphicNFOn g Ω →
      toMeromorphicNFOn f Ω =ᶠ[Filter.codiscreteWithin Ω] toMeromorphicNFOn g Ω

/--
Build the previous codiscrete propagation API from the local-to-global propagation API.

The only nontrivial work here is theorem-backed:
codiscrete equality on the open overlap gives punctured equality at a chosen
overlap point.
-/
def buildOmegaNormalFormCodiscretePropagationFromLocal
    (ONFLP : OmegaNormalFormLocalPropagationAPI) :
    OmegaNormalFormCodiscretePropagationAPI :=
  { h_nf_propagate := fun f g V hVopen hVnonempty hVsubset hf hg hcod =>
      by
        rcases hVnonempty with ⟨z₀, hz₀V⟩
        exact
          ONFLP.h_local_propagate
            f
            g
            z₀
            (hVsubset hz₀V)
            hf
            hg
            (eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_of_mem_open
              hVopen
              hz₀V
              hcod) }

/--
Endpoint after replacing `OmegaNormalFormCodiscretePropagationAPI` by the
local-to-global normal-form propagation API.
-/
theorem finalConditionalRHSpine_localNormalFormPropagation
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (ONFLP : OmegaNormalFormLocalPropagationAPI) :
    RiemannHypothesis :=
  finalConditionalRHSpine
    ZF
    Y
    X
    E
    (buildOmegaNormalFormCodiscretePropagationFromLocal ONFLP)

end

end RHFormalization
