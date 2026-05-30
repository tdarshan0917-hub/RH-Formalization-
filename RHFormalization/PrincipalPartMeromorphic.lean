import Mathlib.Analysis.Meromorphic.Basic
import RHFormalization.PrincipalPartOrderFromCobounded

/-!
# RHFormalization.PrincipalPartMeromorphic

Discharges `PrincipalPartMeromorphicAtAPI`.

From the project-local principal-part definition

`f = coeff / (z - s0) + h`

locally near `s0`, with `h` holomorphic, we prove that `f` is meromorphic at
`s0`.

This does not yet discharge `PrincipalPartCoboundedAPI`; that remains the local
non-removability/coboundedness input.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
The simple principal-part model `coeff / (w - z) + h w` is meromorphic at `z`
when `h` is holomorphic at `z`.
-/
theorem principalPart_model_meromorphicAt
    (h : ℂ → ℂ)
    (z coeff : ℂ)
    (hh : HolomorphicAtC h z) :
    MeromorphicAt (fun w : ℂ => coeff / (w - z) + h w) z := by
  have h_const_an :
      AnalyticAt ℂ (fun _ : ℂ => coeff) z :=
    analyticAt_const

  have h_const_mer :
      MeromorphicAt (fun _ : ℂ => coeff) z :=
    h_const_an.meromorphicAt

  have h_id_an :
      AnalyticAt ℂ (fun w : ℂ => w) z :=
    analyticAt_id

  have h_z_an :
      AnalyticAt ℂ (fun _ : ℂ => z) z :=
    analyticAt_const

  have h_den_an :
      AnalyticAt ℂ (fun w : ℂ => w - z) z :=
    h_id_an.sub h_z_an

  have h_den_mer :
      MeromorphicAt (fun w : ℂ => w - z) z :=
    h_den_an.meromorphicAt

  have h_pole_mer :
      MeromorphicAt (fun w : ℂ => coeff / (w - z)) z := by
    simpa [Pi.div_apply] using
      (h_const_mer.div h_den_mer)

  have h_h_mer :
      MeromorphicAt h z :=
    hh.meromorphicAt

  simpa [Pi.add_apply] using
    (h_pole_mer.add h_h_mer)

/--
A project-local principal part gives meromorphicity at the pole point.
-/
theorem hasPrincipalPartAtC_meromorphicAt
    (f : ℂ → ℂ)
    (z coeff : ℂ)
    (hpp : HasPrincipalPartAtC f z coeff) :
    MeromorphicAt f z := by
  rcases hpp with ⟨h, hh, hlocal⟩

  have h_model_mer :
      MeromorphicAt (fun w : ℂ => coeff / (w - z) + h w) z :=
    principalPart_model_meromorphicAt h z coeff hh

  have h_eq_punct :
      f =ᶠ[𝓝[≠] z] (fun w : ℂ => coeff / (w - z) + h w) := by
    filter_upwards
      [(nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z) hlocal,
       self_mem_nhdsWithin] with w hw hne
    exact hw (by simpa using hne)

  exact h_model_mer.congr h_eq_punct.symm

/--
A principal-part normal form gives meromorphicity at the pole point.
-/
theorem principalPartNormalForm_meromorphicAt
    (f : ℂ → ℂ)
    (z coeff : ℂ)
    (hpp : PrincipalPartNormalForm f z coeff) :
    MeromorphicAt f z :=
  hasPrincipalPartAtC_meromorphicAt f z coeff hpp.h_principalPart

/--
Default theorem-backed implementation of `PrincipalPartMeromorphicAtAPI`.
-/
def defaultPrincipalPartMeromorphicAtAPI :
    PrincipalPartMeromorphicAtAPI :=
  { h_meromorphicAt :=
      principalPartNormalForm_meromorphicAt }

/--
Endpoint after discharging `PrincipalPartMeromorphicAtAPI`.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_principalPartCobounded`,
this theorem no longer requires

`M : PrincipalPartMeromorphicAtAPI`.

It still requires

`C : PrincipalPartCoboundedAPI`.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_principalPartCobounded_only
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (C : PrincipalPartCoboundedAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_principalPartCobounded
    ZF
    Y
    X
    E
    I
    defaultPrincipalPartMeromorphicAtAPI
    C

end

end RHFormalization
