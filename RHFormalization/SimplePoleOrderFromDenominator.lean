import Mathlib.Analysis.Meromorphic.Order
import RHFormalization.DefaultSimplePoleCoboundedFromOrder

/-!
# RHFormalization.SimplePoleOrderFromDenominator

Narrows `SimplePoleNegativeOrderAPI`.

Instead of assuming directly that

`coeff / (w - s0)`

has negative meromorphic order, we reduce it to the single denominator fact:

`meromorphicOrderAt (fun w => w - s0) s0 = 1`.

Mathlib supplies the nonzero-constant order and quotient-order machinery.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter Bornology

/--
Narrow denominator order input.

This is the exact simple-zero fact for the affine denominator `w - s0`.
-/
structure DenominatorSimpleZeroOrderAPI where
  h_denominator_order :
    ∀ s0 : ℂ,
      meromorphicOrderAt (fun w : ℂ => w - s0) s0 =
        ((1 : ℤ) : WithTop ℤ)

/--
A nonzero constant has meromorphic order zero.
-/
theorem meromorphicOrderAt_nonzero_const
    (s0 coeff : ℂ)
    (hcoeff : coeff ≠ 0) :
    meromorphicOrderAt (fun _ : ℂ => coeff) s0 =
      (0 : WithTop ℤ) := by
  classical
  simpa [hcoeff] using
    (meromorphicOrderAt_const (z₀ := s0) (e := coeff))

/--
The quotient of a nonzero constant by a simple-zero denominator has negative
meromorphic order.
-/
theorem simplePole_negative_order_from_denominator
    (D0 : DenominatorSimpleZeroOrderAPI)
    (s0 coeff : ℂ)
    (hcoeff : coeff ≠ 0) :
    meromorphicOrderAt (fun w : ℂ => coeff / (w - s0)) s0 < 0 := by
  have h_num_an :
      AnalyticAt ℂ (fun _ : ℂ => coeff) s0 :=
    analyticAt_const
  have h_num_mer :
      MeromorphicAt (fun _ : ℂ => coeff) s0 :=
    h_num_an.meromorphicAt

  have h_id_an :
      AnalyticAt ℂ (fun w : ℂ => w) s0 :=
    analyticAt_id
  have h_s0_an :
      AnalyticAt ℂ (fun _ : ℂ => s0) s0 :=
    analyticAt_const
  have h_den_an :
      AnalyticAt ℂ (fun w : ℂ => w - s0) s0 :=
    h_id_an.sub h_s0_an
  have h_den_mer :
      MeromorphicAt (fun w : ℂ => w - s0) s0 :=
    h_den_an.meromorphicAt

  have h_div :
      meromorphicOrderAt (fun w : ℂ => coeff / (w - s0)) s0 =
        meromorphicOrderAt (fun _ : ℂ => coeff) s0 -
          meromorphicOrderAt (fun w : ℂ => w - s0) s0 := by
    simpa [Pi.div_apply] using
      (meromorphicOrderAt_div h_num_mer h_den_mer)

  have h_const :
      meromorphicOrderAt (fun _ : ℂ => coeff) s0 =
        (0 : WithTop ℤ) :=
    meromorphicOrderAt_nonzero_const s0 coeff hcoeff

  have h_den :
      meromorphicOrderAt (fun w : ℂ => w - s0) s0 =
        ((1 : ℤ) : WithTop ℤ) :=
    D0.h_denominator_order s0

  have h_eq :
      meromorphicOrderAt (fun w : ℂ => coeff / (w - s0)) s0 =
        ((-1 : ℤ) : WithTop ℤ) := by
    rw [h_div, h_const, h_den]
    norm_num

  have h_neg :
      ((-1 : ℤ) : WithTop ℤ) < 0 := by
    rw [← WithTop.coe_zero]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)

  simpa [h_eq] using h_neg

/--
Build `SimplePoleNegativeOrderAPI` from the denominator simple-zero order fact.
-/
def buildSimplePoleNegativeOrderAPIFromDenominator
    (D0 : DenominatorSimpleZeroOrderAPI) :
    SimplePoleNegativeOrderAPI :=
  { h_simple_pole_negative_order :=
      simplePole_negative_order_from_denominator D0 }

/--
Endpoint after replacing `SimplePoleNegativeOrderAPI` by the denominator
simple-zero order input.
-/
theorem mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_denominatorOrder
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI)
    (I : MeromorphicIdentityPrincipleAPI)
    (D0 : DenominatorSimpleZeroOrderAPI) :
    RiemannHypothesis :=
  mainTheorem_from_default_connectedOmega_meromorphicAlgebra_and_simplePoleOrder
    ZF
    Y
    X
    E
    I
    (buildSimplePoleNegativeOrderAPIFromDenominator D0)

end

end RHFormalization
