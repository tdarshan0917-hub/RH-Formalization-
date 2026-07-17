import RHFormalization.AdmissibleFreeFH
import RHFormalization.AdmissiblePrimeFirstOrderSplit
import RHFormalization.DBFFBcorr
import Mathlib

/-!
# DBFFGate2WindowError

This file freezes the exact signed Gate-2 object.

`FirstOrderWindow` is the first-order genuine-operator correction and already
contains its minus sign.

`Bcorr` is the already-banked corrected B-side term:
`BcorrWin + compensatorM`.

The only remaining analytic Gate-2 problem is to prove that
`gate2WindowError` is compact-uniformly bounded / vanishing.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex Filter
open scoped Topology BigOperators

/-- **The exact Gate-2 window error.**

This is not the second-order Duhamel term. It compares the first-order operator
window against the corrected one-letter prime package.
-/
noncomputable def gate2WindowError (n : ℕ) (s : ℂ) : ℂ :=
  FirstOrderWindow n s
    - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
    + Bcorr n s

/-- **Exact corrected-residual decomposition.**

This theorem fixes all signs and normalizations before any analytic estimate:

`R_stage + Bcorr = FreeStage + Gate2WindowError + SecondResidual`.
-/
theorem correctedResidual_eq_free_add_gate2_add_second
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
        + Bcorr n s
      =
    admissibleFreeStage n s
      + gate2WindowError n s
      + SecondResolventResidual n s := by
  have hR :
      galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
        =
      galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := rfl

  have hF :
      galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        =
      admissibleFreeStage n s + FadmPrimeStage n s := by
    unfold FadmPrimeStage
    ring

  have hsplit :
      FadmPrimeStage n s
        =
      FirstOrderWindow n s + SecondResolventResidual n s :=
    FadmPrimeStage_eq_first_plus_second n hs

  rw [hR, hF, hsplit]
  unfold gate2WindowError
  ring

#print axioms gate2WindowError
#print axioms correctedResidual_eq_free_add_gate2_add_second

end RHFormalization
