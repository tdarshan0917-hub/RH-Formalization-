-- SENTINEL: spike-transfer-at-stage-v1
import RHFormalization.SpikeTransferPillarClose
import Mathlib

/-! # Pillar 2 opener — pillar 1 instantiated at the decoded adaptive stage.
The M=2 identity and the `t²` remainder bound, at `qs := active codes at
admR n`, `L := admL n`, `N := admN n`, weights `ppWeightReal`: the exact
objects the live route consumes. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- **The M=2 expansion at stage `n`.** -/
theorem spikeTransfer_M2_form_at_stage (n : ℕ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := admN n) (admL n)
        + galerkinV (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n))
            ppWeightReal (admL n))))).trace
      = (NormedSpace.exp (t • (-(galerkinK (N := admN n) (admL n))))).trace
        - t * (∑ m : Fin (admN n),
            galerkinV (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n))
              ppWeightReal (admL n) m m
            * Real.exp (-(t * galerkinLam (admL n) (m : ℕ))))
        + spikeTransferE2 (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n))
            ppWeightReal (admL n) t :=
  spikeTransfer_M2_form (N := admN n) 1
    (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n) t

/-- **The remainder bound at stage `n`.** -/
theorem spikeTransferE2_abs_le_t_sq_at_stage (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |spikeTransferE2 (N := admN n) 1
        (activePrimePowerCodesCenterBelow (admR n))
        ppWeightReal (admL n) t|
      ≤ (Real.sqrt ((admN n : ℝ) * frobSq (galerkinV (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n))
            ppWeightReal (admL n)))
          * ((admN n : ℝ)^2
            * Real.sqrt (frobSq (galerkinV (N := admN n) 1
                (activePrimePowerCodesCenterBelow (admR n))
                ppWeightReal (admL n)))))
        * t^2 :=
  spikeTransferE2_abs_le_t_sq (N := admN n)
    (activePrimePowerCodesCenterBelow (admR n)) (admL n) (admL_pos n) t ht

#print axioms spikeTransfer_M2_form_at_stage
#print axioms spikeTransferE2_abs_le_t_sq_at_stage

end

end RHFormalization
