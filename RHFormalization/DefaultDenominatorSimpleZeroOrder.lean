import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.SimplePoleOrderFromDenominator

/-!
# RHFormalization.DefaultDenominatorSimpleZeroOrder

Discharges `DenominatorSimpleZeroOrderAPI`.

We prove the local denominator fact

`meromorphicOrderAt (fun w => w - s0) s0 = 1`.

This is the final local simple-pole order input used by the local pole-obstruction
chain.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter Bornology

/--
The affine denominator `w - s0` has analytic order one at `s0`.
-/
theorem analyticOrderAt_sub_self_eq_one
    (s0 : ℂ) :
    analyticOrderAt (fun w : ℂ => w - s0) s0 = 1 := by
  have hid :
      AnalyticAt ℂ (fun w : ℂ => w) s0 :=
    analyticAt_id

  have hderiv_ne :
      deriv (fun w : ℂ => w) s0 ≠ 0 := by
    simpa using (by norm_num : (1 : ℂ) ≠ 0)

  have hmain :
      analyticOrderAt
        (fun w : ℂ => (fun u : ℂ => u) w - (fun u : ℂ => u) s0)
        s0 = 1 :=
    hid.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv_ne

  simpa using hmain

/--
The affine denominator `w - s0` has meromorphic order one at `s0`.
-/
theorem meromorphicOrderAt_sub_self_eq_one
    (s0 : ℂ) :
    meromorphicOrderAt (fun w : ℂ => w - s0) s0 =
      ((1 : ℤ) : WithTop ℤ) := by
  have hid :
      AnalyticAt ℂ (fun w : ℂ => w) s0 :=
    analyticAt_id

  have hconst :
      AnalyticAt ℂ (fun _ : ℂ => s0) s0 :=
    analyticAt_const

  have hden_an :
      AnalyticAt ℂ (fun w : ℂ => w - s0) s0 := by
    simpa using hid.sub hconst

  have horder :
      analyticOrderAt (fun w : ℂ => w - s0) s0 = 1 :=
    analyticOrderAt_sub_self_eq_one s0

  rw [hden_an.meromorphicOrderAt_eq, horder]
  norm_num

/--
Default implementation of `DenominatorSimpleZeroOrderAPI`.
-/
def defaultDenominatorSimpleZeroOrderAPI :
    DenominatorSimpleZeroOrderAPI :=
  { h_denominator_order :=
      meromorphicOrderAt_sub_self_eq_one }

/--
Endpoint after discharging `DenominatorSimpleZeroOrderAPI`.

Compared with
`mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_denominatorOrder`,
this theorem no longer requires

`D0 : DenominatorSimpleZeroOrderAPI`.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_localPoleClosed
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_denominatorOrder
    ZF
    Y
    X
    E
    I
    defaultDenominatorSimpleZeroOrderAPI

end

end RHFormalization
