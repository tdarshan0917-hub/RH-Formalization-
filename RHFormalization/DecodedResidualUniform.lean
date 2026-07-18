-- SENTINEL: decoded-residual-uniform-v4
import RHFormalization.DecodedColumnNormBound
import RHFormalization.DecodedAdaptivePrimeSplit
import RHFormalization.AdmissibleResidualUniform
import RHFormalization.AdmissibleResidualAssembly
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

noncomputable def decodedAdaptivePerturbedLam (c : ℝ) (n : ℕ) :
    Fin (adaptiveN c n) → ℝ :=
  perturbedEigenvalues (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
    (decodedGalerkinVC_isHermitian (N := adaptiveN c n) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
      (adaptiveL c n))

theorem decodedSecondResolventResidual_norm_le
    (c : ℝ) (n : ℕ) (s : ℂ) {δ C₀ : ℝ} (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (hlow : ∀ i, δ ≤ ‖s + (SupVConst : ℂ)
        + ((decodedAdaptivePerturbedLam c n i : ℝ) : ℂ)‖)
    (hbound : ∀ lam : ℝ, 0 ≤ lam →
        ‖(s + (SupVConst : ℂ) + (lam : ℂ))⁻¹‖ ≤ C₀ * (1 + lam)⁻¹) :
    ‖decodedAdaptiveSecondResolventResidual c n s‖
      ≤ 1 / (2 * adaptiveL c n) *
          (δ⁻¹ * (C₀ ^ 2 * adaptiveL c n *
            ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2))) := by
  classical
  have hL : (0 : ℝ) < adaptiveL c n := adaptiveL_pos c n
  have h2L : (0 : ℝ) < 2 * adaptiveL c n := mul_pos (by norm_num) hL
  -- the eigenvalue-floor hypothesis in raw `perturbedEigenvalues` form
  have hlow' : ∀ i : Fin (adaptiveN c n), δ ≤ ‖s + (SupVConst : ℂ)
      + ((perturbedEigenvalues (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
            (decodedGalerkinVC_isHermitian (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n)) i : ℝ) : ℂ)‖ := by
    intro i
    have h := hlow i
    first
      | exact h
      | (unfold decodedAdaptivePerturbedLam at h; exact h)
      | simpa [admPerturbedLam] using h
  -- BRICK 4b-ii at the shifted point
  have htr := trace_RD_V_RH_V_RD_norm_le_weighted_columns
      (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
      (decodedGalerkinVC_isHermitian (N := adaptiveN c n) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (adaptiveL c n))
      (s + (SupVConst : ℂ)) hδ hlow'
  -- BRICK 4b-iii(b): uniform column bound
  have hcol : ∀ m : Fin (adaptiveN c n),
      ‖Matrix.toEuclideanLin
          (decodedGalerkinVC (N := adaptiveN c n) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (adaptiveL c n)) (stdBasisE (adaptiveN c n) m)‖ ^ 2
        ≤ (adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2 :=
    fun m => decodedGalerkinVC_column_norm_sq_le (admR n) (adaptiveL c n) hL m
  -- BRICK 4b-iii(a) at the shifted point
  have hwsum := freeMu_resolvent_sq_sum_le (adaptiveN c n) (adaptiveL c n) hL
      (s + (SupVConst : ℂ)) C₀ hC₀ hbound
  have hB0 : (0 : ℝ)
      ≤ (adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2 := by
    positivity
  -- combine: Σ (weight² · column²) ≤ (C₀²L) · N((2/L)S₁)²
  have hsum :
      ∑ m : Fin (adaptiveN c n),
        ‖(s + (SupVConst : ℂ)
            + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹‖ ^ 2
          * ‖Matrix.toEuclideanLin
              (decodedGalerkinVC (N := adaptiveN c n) 1
                (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                (adaptiveL c n)) (stdBasisE (adaptiveN c n) m)‖ ^ 2
        ≤ C₀ ^ 2 * adaptiveL c n
            * ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2) := by
    have h1 :
        ∑ m : Fin (adaptiveN c n),
          ‖(s + (SupVConst : ℂ)
              + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹‖ ^ 2
            * ‖Matrix.toEuclideanLin
                (decodedGalerkinVC (N := adaptiveN c n) 1
                  (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                  (adaptiveL c n)) (stdBasisE (adaptiveN c n) m)‖ ^ 2
          ≤ ∑ m : Fin (adaptiveN c n),
              ‖(s + (SupVConst : ℂ)
                  + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹‖ ^ 2
                * ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2) :=
      Finset.sum_le_sum fun m _ =>
        mul_le_mul_of_nonneg_left (hcol m) (sq_nonneg _)
    have h2 :
        ∑ m : Fin (adaptiveN c n),
          ‖(s + (SupVConst : ℂ)
              + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹‖ ^ 2
            * ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2)
          = (∑ m : Fin (adaptiveN c n),
              ‖(s + (SupVConst : ℂ)
                  + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹‖ ^ 2)
              * ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2) := by
      first
        | rw [Finset.sum_mul]
        | rw [← Finset.sum_mul]
    have h3 :
        (∑ m : Fin (adaptiveN c n),
            ‖(s + (SupVConst : ℂ)
                + ((galerkinFreeMu (adaptiveN c n) (adaptiveL c n) m : ℝ) : ℂ))⁻¹‖ ^ 2)
            * ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2)
          ≤ C₀ ^ 2 * adaptiveL c n
              * ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2) :=
      mul_le_mul_of_nonneg_right hwsum hB0
    exact le_trans h1 (le_trans (le_of_eq h2) h3)
  -- density-constant norm
  have hdens : ‖admDensityC n‖ = 1 / (2 * adaptiveL c n) := by
    unfold admDensityC
    first
      | rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr h2L)]
      | rw [Complex.norm_ofReal, abs_of_pos (one_div_pos.mpr h2L)]
  -- assemble
  unfold decodedAdaptiveSecondResolventResidual
  rw [norm_mul, hdens]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.mpr h2L))
  exact le_trans htr
    (mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hδ)))


/-- Schedule collapse: master RHS uniformly ≤ C₀³·146. -/
theorem decoded_residual_schedule_collapse (c : ℝ) (n : ℕ)
    {C₀ : ℝ} (hC₀ : 0 < C₀) :
    1 / (2 * adaptiveL c n) *
        (C₀ * (C₀ ^ 2 * adaptiveL c n *
          ((adaptiveN c n : ℝ)
            * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2)))
      ≤ C₀ ^ 3 * 146 := by
  have hLad : (0:ℝ) < adaptiveL c n := adaptiveL_pos c n
  have hLle : admL n ≤ adaptiveL c n := admL_le_adaptiveL c n
  have hadmLeq : admL n = ((n:ℝ)+2)^3 := by
    first | rfl | (unfold admL; ring) | (unfold admL; push_cast; ring)
  have hx : (2:ℝ) ≤ (n:ℝ)+2 := by
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hxpos : (0:ℝ) < (n:ℝ)+2 := by linarith
  have hLx : ((n:ℝ)+2)^3 ≤ adaptiveL c n := by rw [← hadmLeq]; exact hLle
  have hS1 : S1mass (admR n) ≤ 4 * ((n:ℝ)+2) := by
    have h1 := S1mass_le (admR n)
    have hexp : Real.exp (admR n) ≤ (n:ℝ)+2 := by
      have hR : admR n = Real.log ((n:ℝ)+2) / 2 := by
        first | rfl | (unfold admR; ring) | (unfold admR; push_cast; ring)
      rw [hR]
      have hlog : (0:ℝ) ≤ Real.log ((n:ℝ)+2) := by
        apply Real.log_nonneg; linarith
      calc Real.exp (Real.log ((n:ℝ)+2) / 2)
          ≤ Real.exp (Real.log ((n:ℝ)+2)) := by
            apply Real.exp_le_exp.mpr; linarith
        _ = (n:ℝ)+2 := Real.exp_log hxpos
    calc S1mass (admR n) ≤ 2 * (Real.exp (admR n) + 2) := h1
      _ ≤ 2 * (((n:ℝ)+2) + ((n:ℝ)+2)) := by linarith
      _ = 4 * ((n:ℝ)+2) := by ring
  have hS1nn : (0:ℝ) ≤ S1mass (admR n) := S1mass_nonneg _
  have hprod : (0:ℝ) ≤ adaptiveL c n * ((n:ℝ)+2) := by positivity
  have hNle : (adaptiveN c n : ℝ)
      ≤ ((n:ℝ)+2)^4 + (adaptiveL c n * ((n:ℝ)+2) + 1) := by
    have hadmN : (admN n : ℝ) ≤ ((n:ℝ)+2)^4 := by
      have he : (admN n : ℝ) = ((n:ℝ)+2)^4 := by
        first | (unfold admN; push_cast; ring) | (simp [admN]; push_cast; ring)
      linarith
    have hceil : ((⌈adaptiveL c n * ((n:ℝ)+2)⌉ₓ : ℕ) : ℝ)
        ≤ adaptiveL c n * ((n:ℝ)+2) + 1 := by
      first
        | exact Nat.ceil_le_add_one hprod
        | exact le_of_lt (Nat.ceil_lt_add_one hprod)
    have hNdef : adaptiveN c n = max (admN n) ⌈adaptiveL c n * ((n:ℝ)+2)⌉ₓ := by
      first | rfl | (unfold adaptiveN; rfl)
    rw [hNdef]
    push_cast
    apply max_le
    · linarith
    · have h4 : (0:ℝ) ≤ ((n:ℝ)+2)^4 := by positivity
      linarith
  have h8 : (8:ℝ) ≤ adaptiveL c n := by
    first
      | exact eight_le_adaptiveL c n
      | (refine le_trans ?_ hLx; nlinarith [hx])
  have h1 : ((n:ℝ)+2)^4 ≤ adaptiveL c n * ((n:ℝ)+2) := by
    nlinarith [hLx, hxpos.le]
  have h2 : (1:ℝ) ≤ adaptiveL c n * ((n:ℝ)+2) := by nlinarith [h8, hx]
  have hN3 : (adaptiveN c n : ℝ) ≤ 3 * (adaptiveL c n * ((n:ℝ)+2)) := by
    nlinarith [hNle, h1, h2]
  have hLHS : 1 / (2 * adaptiveL c n) *
      (C₀ * (C₀ ^ 2 * adaptiveL c n *
        ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2)))
      = 2 * C₀ ^ 3 * ((adaptiveN c n : ℝ) * S1mass (admR n) ^ 2)
          / adaptiveL c n ^ 2 := by
    field_simp
    try ring
  rw [hLHS]
  have hNnn : (0:ℝ) ≤ (adaptiveN c n : ℝ) := Nat.cast_nonneg _
  have hS1sq : S1mass (admR n) ^ 2 ≤ 16 * ((n:ℝ)+2)^2 := by
    nlinarith [hS1, hS1nn]
  have hnum : (adaptiveN c n : ℝ) * S1mass (admR n) ^ 2
      ≤ 48 * (adaptiveL c n * ((n:ℝ)+2)^3) := by
    calc (adaptiveN c n : ℝ) * S1mass (admR n) ^ 2
        ≤ (3 * (adaptiveL c n * ((n:ℝ)+2))) * (16 * ((n:ℝ)+2)^2) := by
          apply mul_le_mul hN3 hS1sq (by positivity) (by positivity)
      _ = 48 * (adaptiveL c n * ((n:ℝ)+2)^3) := by ring
  have hden : adaptiveL c n * ((n:ℝ)+2)^3 ≤ adaptiveL c n ^ 2 := by
    nlinarith [hLx, hLad.le]
  have hfrac : (adaptiveN c n : ℝ) * S1mass (admR n) ^ 2 / adaptiveL c n ^ 2
      ≤ 73 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < adaptiveL c n ^ 2)]
    nlinarith [hnum, hden]
  calc 2 * C₀ ^ 3 * ((adaptiveN c n : ℝ) * S1mass (admR n) ^ 2)
        / adaptiveL c n ^ 2
      = 2 * C₀ ^ 3 * ((adaptiveN c n : ℝ) * S1mass (admR n) ^ 2
          / adaptiveL c n ^ 2) := by ring
    _ ≤ 2 * C₀ ^ 3 * 73 := by
        apply mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = C₀ ^ 3 * 146 := by ring

#print axioms decodedSecondResolventResidual_norm_le
#print axioms decoded_residual_schedule_collapse

end

end RHFormalization
