import RHFormalization.SeamCoreFactoredForm
import RHFormalization.DBFFStarObject
import Mathlib

/-!
# SeamStarUnification — seamCore IS the (★) object, by banked identity

ROUTE CARD
1. Target: `seamCore = (2√(s+1/4))⁻¹ · starObject` on Ω — two lines over
   the banked D.OP.2 identity `B_sub_compensator_eq`, since
   `seamCore = B_stage − compensatorM` by rfl. Plus the conditional
   transfer: seamCore control from an O3 (starObject) bound.
2. Consequence: the P2-4 campaign and obligation O3 are ONE obligation,
   kernel-certified. `starObject_bounded_off_parabola` is banked; the
   sole open content is O3 AT PARABOLA DEPTH (DBFFO3ParabolaDepthHstar),
   to be supplied by the operator side (spike-transfer/FK).
3. Raw B on Ω? NO. B−M bare Prop? NO — hypothesis slot only.
4. Consumer: correctedResidual_locbdd_of_seamCore → provider →
   RcanCandidate → HtailExists.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

theorem invSqrtFactor_ne_zero {s : ℂ} (hs : s ∈ Ω) :
    invSqrtFactor s ≠ 0 := by
  unfold invSqrtFactor
  exact inv_ne_zero (mul_ne_zero two_ne_zero (sqrt_ne_zero' hs))

/-- **seamCore = prefactor · starObject** — the P2-4 object and the frozen
O3 object are one object (banked D.OP.2). -/
theorem seamCore_eq_prefactor_mul_starObject (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    seamCore n s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) * starObject n s := by
  calc seamCore n s
      = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - compensatorM n s := rfl
    _ = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) * starObject n s :=
        B_sub_compensator_eq n hs

/-- **seamCore control from O3.** The `hstar` hypothesis is obligation O3;
off-parabola it is banked (`starObject_bounded_off_parabola`); at parabola
depth it is the operator-side frontier. -/
theorem seamCore_bounded_of_starObject_bounded
    (K : Set ℂ) (hKΩ : K ⊆ Ω)
    (c : ℝ) (hc : 0 < c)
    (hker : ∀ s ∈ K, ‖(1:ℂ) / (2 * Complex.sqrt (s + (1/4:ℂ)))‖ ≤ c⁻¹)
    (Cstar : ℝ)
    (hstar : ∀ n : ℕ, ∀ s ∈ K, ‖starObject n s‖ ≤ Cstar) :
    ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ c⁻¹ * Cstar := by
  intro n s hsK
  have hsΩ : s ∈ Ω := hKΩ hsK
  rw [seamCore_eq_prefactor_mul_starObject n hsΩ, norm_mul]
  have hC0 : (0:ℝ) ≤ Cstar := le_trans (norm_nonneg _) (hstar n s hsK)
  have hc0 : (0:ℝ) ≤ c⁻¹ := (inv_pos.mpr hc).le
  exact mul_le_mul (hker s hsK) (hstar n s hsK) (norm_nonneg _) hc0

#print axioms invSqrtFactor_ne_zero
#print axioms seamCore_eq_prefactor_mul_starObject
#print axioms seamCore_bounded_of_starObject_bounded

end

end RHFormalization
