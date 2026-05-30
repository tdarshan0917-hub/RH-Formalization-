import Mathlib
import RHFormalization.PrincipalPartMeromorphic

/-!
# RHFormalization.PrincipalPartCoboundedModel

Narrows `PrincipalPartCoboundedAPI`.

Instead of assuming coboundedness for every bundled `PrincipalPartNormalForm`, we reduce it
to the exact simple-pole-plus-holomorphic local model:

`coeff / (w - s0) + h w`

with `coeff ≠ 0` and `h` holomorphic at `s0`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Narrow local analytic input:

a nonzero simple-pole term plus a holomorphic function tends to infinity/cobounded
on the punctured neighbourhood.
-/
structure SimplePolePlusHolomorphicCoboundedAPI where
  h_model_cobounded :
    ∀ (h : ℂ → ℂ) (s0 coeff : ℂ),
      coeff ≠ 0 →
      HolomorphicAtC h s0 →
        Tendsto
          (fun w : ℂ => coeff / (w - s0) + h w)
          (𝓝[≠] s0)
          (Bornology.cobounded ℂ)

/--
Build `PrincipalPartCoboundedAPI` from the narrower simple-pole-plus-holomorphic
coboundedness input.
-/
def buildPrincipalPartCoboundedAPIFromModel
    (S : SimplePolePlusHolomorphicCoboundedAPI) :
    PrincipalPartCoboundedAPI :=
  { h_cobounded := fun f s0 coeff hpp =>
      by
        rcases hpp.h_principalPart with ⟨h, hh, hlocal⟩

        have h_model :
            Tendsto
              (fun w : ℂ => coeff / (w - s0) + h w)
              (𝓝[≠] s0)
              (Bornology.cobounded ℂ) :=
          S.h_model_cobounded h s0 coeff hpp.h_coeff_ne_zero hh

        have h_eq :
            f =ᶠ[𝓝[≠] s0] (fun w : ℂ => coeff / (w - s0) + h w) := by
          filter_upwards
            [(nhdsWithin_le_nhds : 𝓝[≠] s0 ≤ 𝓝 s0) hlocal,
             self_mem_nhdsWithin] with w hw hne
          exact hw (by simpa using hne)

        exact h_model.congr' h_eq.symm }

/--
Endpoint after replacing `PrincipalPartCoboundedAPI` by the narrower
`SimplePolePlusHolomorphicCoboundedAPI`.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_principalPartCobounded_only`,
this theorem no longer asks for:

`C : PrincipalPartCoboundedAPI`.

It asks only for the local model coboundedness theorem.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_simplePoleCobounded
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (S : SimplePolePlusHolomorphicCoboundedAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_principalPartCobounded_only
    ZF
    Y
    X
    E
    I
    (buildPrincipalPartCoboundedAPIFromModel S)

end

end RHFormalization
