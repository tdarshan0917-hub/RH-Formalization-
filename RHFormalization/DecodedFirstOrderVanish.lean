-- SENTINEL: decoded-fow-vanish-v1
import RHFormalization.DecodedAdaptivePrimeSplit
import RHFormalization.DecodedColumnNormBound
import RHFormalization.AdmissibleFirstOrderDiagonal
import RHFormalization.AdmissibleResolventWeightSum
import RHFormalization.AdmissibleFirstOrderVanish
import Mathlib

/-!
# DecodedFirstOrderVanish — brick 1c of hShort
Decoded FOW uniform bound via the generic trace_RD_V_RD engine (V-generic,
banked), the decoded entry bound (banked, brick 1a/1b), the resolvent-weight
sum (banked), and the fow collapse arithmetic (banked). Chain:
‖decodedFOW‖ ≤ (1/2Lad)·((2/Lad)·S₁)·(C₀²·Lad) = C₀²·S₁/Lad ≤ C₀²·S₁/admL
≤ 6C₀²/(n+2) — the schedule transfer via banked admL_le_adaptiveL.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/-- Decoded FOW diagonal form: generic engine at the decoded V. -/
theorem decodedFirstOrderWindow_eq_diag_sum (c : ℝ) (n : ℕ) (s : ℂ) :
    decodedAdaptiveFirstOrderWindow c n s
      = -(adaptiveDensityC c n *
          ∑ m : Fin (adaptiveN c n),
            (decodedGalerkinVC (N := adaptiveN c n) 1
                (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                (adaptiveL c n)) m m
              * (((s + (SupVConst : ℂ))
                  + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹) ^ 2) := by
  unfold decodedAdaptiveFirstOrderWindow
  rw [trace_RD_V_RD]

/-- Decoded FOW pointwise master bound. -/
theorem decodedFirstOrderWindow_norm_le (c : ℝ) (n : ℕ) (s : ℂ)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hbound : ∀ lam : ℝ, 0 ≤ lam →
        ‖(s + (SupVConst : ℂ) + (lam : ℂ))⁻¹‖ ≤ C₀ * (1 + lam)⁻¹) :
    ‖decodedAdaptiveFirstOrderWindow c n s‖
      ≤ 1 / (2 * adaptiveL c n)
          * (2 / adaptiveL c n * S1mass (admR n)
              * (C₀ ^ 2 * adaptiveL c n)) := by
  have hL : (0 : ℝ) < adaptiveL c n := adaptiveL_pos c n
  have h2L : (0 : ℝ) < 2 * adaptiveL c n := by positivity
  have hdens : ‖adaptiveDensityC c n‖ = 1 / (2 * adaptiveL c n) := by
    unfold adaptiveDensityC
    first
      | rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr h2L)]
      | rw [Complex.norm_ofReal, abs_of_pos (one_div_pos.mpr h2L)]
  rw [decodedFirstOrderWindow_eq_diag_sum c n s, norm_neg, norm_mul, hdens]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.mpr h2L))
  have hentry : ∀ m : Fin (adaptiveN c n),
      ‖(decodedGalerkinVC (N := adaptiveN c n) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (adaptiveL c n)) m m‖
        ≤ 2 / adaptiveL c n * S1mass (admR n) := by
    intro m
    have hVC : (decodedGalerkinVC (N := adaptiveN c n) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (adaptiveL c n)) m m
        = ((decodedGalerkinV (N := adaptiveN c n) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (adaptiveL c n) m m : ℝ) : ℂ) := rfl
    rw [hVC]
    first
      | (rw [Complex.norm_real]
         exact abs_decodedGalerkinV_entry_le_S1 (admR n) (adaptiveL c n) hL m m)
      | (rw [Complex.norm_real, Real.norm_eq_abs]
         exact abs_decodedGalerkinV_entry_le_S1 (admR n) (adaptiveL c n) hL m m)
      | (rw [Complex.norm_ofReal]
         exact abs_decodedGalerkinV_entry_le_S1 (admR n) (adaptiveL c n) hL m m)
  have hres := freeMu_resolvent_sq_sum_le (adaptiveN c n) (adaptiveL c n) hL
      (s + (SupVConst : ℂ)) C₀ hC₀ hbound
  have hstep : ∀ m : Fin (adaptiveN c n),
      ‖(decodedGalerkinVC (N := adaptiveN c n) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
          (adaptiveL c n)) m m
        * (((s + (SupVConst : ℂ))
            + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹) ^ 2‖
      ≤ 2 / adaptiveL c n * S1mass (admR n)
          * ‖((s + (SupVConst : ℂ))
              + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹‖ ^ 2 := by
    intro m
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hentry m) (by positivity)
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun m _ => hstep m)) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hres
    (mul_nonneg (by positivity) (S1mass_nonneg _))

/-- **Decoded Gate 2, K-uniform decay**: `‖decodedFOW‖ ≤ C/(n+2)`. -/
theorem decodedFirstOrderWindow_uniform_bound (c : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), ∀ s ∈ K,
      ‖decodedAdaptiveFirstOrderWindow c n s‖ ≤ C / ((n : ℝ) + 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := inv_norm_le_on_compact K hK hKO
  refine ⟨6 * C₀ ^ 2, by positivity, fun n s hs => ?_⟩
  have hbound' : ∀ lam : ℝ, 0 ≤ lam →
      ‖(s + (SupVConst : ℂ) + (lam : ℂ))⁻¹‖ ≤ C₀ * (1 + lam)⁻¹ := by
    intro lam hlam
    have h1 := hC₀ s hs (SupVConst + lam)
      (add_nonneg SupVConst_nonneg_adm hlam)
    have hcast : s + ((SupVConst + lam : ℝ) : ℂ)
        = s + (SupVConst : ℂ) + (lam : ℂ) := by
      push_cast
      ring
    rw [hcast] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hC₀pos.le)
    have hpos : (0 : ℝ) < 1 + lam := by linarith
    have hle : (1 : ℝ) + lam ≤ 1 + (SupVConst + lam) := by
      have hsv := SupVConst_nonneg_adm
      linarith
    first
      | gcongr
      | exact inv_le_inv_of_le hpos hle
  refine le_trans (decodedFirstOrderWindow_norm_le c n s hC₀pos.le hbound') ?_
  -- collapse: RHS = S₁·C₀²/Lad ≤ S₁·C₀²/admL, then banked fow collapse at admL
  have hLad : (0 : ℝ) < adaptiveL c n := adaptiveL_pos c n
  have hLadm : (0 : ℝ) < admL n := admL_pos' n
  have hLle : admL n ≤ adaptiveL c n := admL_le_adaptiveL c n
  have hS0 : (0 : ℝ) ≤ S1mass (admR n) := S1mass_nonneg _
  have hmono : 1 / (2 * adaptiveL c n)
      * (2 / adaptiveL c n * S1mass (admR n) * (C₀ ^ 2 * adaptiveL c n))
      ≤ 1 / (2 * admL n)
      * (2 / admL n * S1mass (admR n) * (C₀ ^ 2 * admL n)) := by
    have hlhs : 1 / (2 * adaptiveL c n)
        * (2 / adaptiveL c n * S1mass (admR n) * (C₀ ^ 2 * adaptiveL c n))
        = S1mass (admR n) * C₀ ^ 2 / adaptiveL c n := by
      field_simp
      try ring
    have hrhs : 1 / (2 * admL n)
        * (2 / admL n * S1mass (admR n) * (C₀ ^ 2 * admL n))
        = S1mass (admR n) * C₀ ^ 2 / admL n := by
      field_simp
      try ring
    rw [hlhs, hrhs]
    apply div_le_div_of_nonneg_left (by positivity) hLadm hLle
  refine le_trans hmono ?_
  have hLeq : admL n = ((n : ℝ) + 2) ^ 3 := by
    first
      | rfl
      | (unfold admL; ring)
      | simp [admL]
  rw [hLeq]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact fow_master_collapse ((n : ℝ) + 2) (S1mass (admR n)) C₀
    (by linarith) hC₀pos.le hS0 (S1mass_admR_le_linear n)

#print axioms decodedFirstOrderWindow_eq_diag_sum
#print axioms decodedFirstOrderWindow_norm_le
#print axioms decodedFirstOrderWindow_uniform_bound

end

end RHFormalization
