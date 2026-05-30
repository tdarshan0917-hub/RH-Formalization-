import RHFormalization.OmegaMeromorphicLocalPropagationEndpoint

/-!
# RHFormalization.OmegaMeromorphicZeroPropagationEndpoint

Narrows `OmegaMeromorphicLocalPropagationAPI`.

The remaining F-side identity theorem is reduced to the zero case:

If a meromorphic function on Ω is zero on a punctured neighbourhood of one point
of Ω, then it is zero on a codiscrete subset of Ω.

Equality propagation for two meromorphic functions follows by applying this zero
propagation theorem to their difference.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Ω-local meromorphic zero propagation.

This is the zero-function form of the remaining Appendix-F identity theorem.
-/
structure OmegaMeromorphicZeroPropagationAPI where
  h_zero_propagate :
    ∀ (H : ℂ → ℂ) (z₀ : ℂ),
      z₀ ∈ Ω →
      MeromorphicOnC H Ω →
      H =ᶠ[𝓝[≠] z₀] (fun _ : ℂ => 0) →
      H =ᶠ[Filter.codiscreteWithin Ω] (fun _ : ℂ => 0)

/--
Build local meromorphic equality propagation from zero propagation by applying
zero propagation to `F - G`.
-/
def buildOmegaMeromorphicLocalPropagationFromZero
    (ZP : OmegaMeromorphicZeroPropagationAPI) :
    OmegaMeromorphicLocalPropagationAPI :=
  { h_local_propagate := fun F G z₀ hz hF hG hlocal =>
      by
        have hdiff_mer :
            MeromorphicOnC (fun s : ℂ => F s - G s) Ω := by
          simpa [Pi.sub_apply] using hF.sub hG

        have hdiff_local :
            (fun s : ℂ => F s - G s) =ᶠ[𝓝[≠] z₀] (fun _ : ℂ => 0) := by
          filter_upwards [hlocal] with s hs
          exact sub_eq_zero.mpr hs

        have hdiff_global :
            (fun s : ℂ => F s - G s) =ᶠ[Filter.codiscreteWithin Ω] (fun _ : ℂ => 0) :=
          ZP.h_zero_propagate
            (fun s : ℂ => F s - G s)
            z₀
            hz
            hdiff_mer
            hdiff_local

        filter_upwards [hdiff_global] with s hs
        exact sub_eq_zero.mp hs }

/--
Endpoint after replacing meromorphic local equality propagation by meromorphic
zero propagation.
-/
theorem finalConditionalRHSpine_meromorphicZeroPropagation
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (ZP : OmegaMeromorphicZeroPropagationAPI) :
    RiemannHypothesis :=
  finalConditionalRHSpine_meromorphicLocalPropagation
    ZF
    Y
    X
    E
    (buildOmegaMeromorphicLocalPropagationFromZero ZP)

end

end RHFormalization
