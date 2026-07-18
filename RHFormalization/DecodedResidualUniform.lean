-- SENTINEL: decoded-residual-uniform-v6
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
  -- density-constant norm (FIX v5: the residual carries adaptiveDensityC, not admDensityC)
  have hdens : ‖adaptiveDensityC c n‖ = 1 / (2 * adaptiveL c n) := by
    unfold adaptiveDensityC
    first
      | rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr h2L)]
      | rw [Complex.norm_ofReal, abs_of_pos (one_div_pos.mpr h2L)]
      | simp [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr h2L)]
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
  have hLne : adaptiveL c n ≠ 0 := ne_of_gt hLad
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
    have hceil : ((⌈adaptiveL c n * ((n:ℝ)+2)⌉₊ : ℕ) : ℝ)
        ≤ adaptiveL c n * ((n:ℝ)+2) + 1 := by
      first
        | exact Nat.ceil_le_add_one hprod
        | exact le_of_lt (Nat.ceil_lt_add_one hprod)
    have hNdef : adaptiveN c n = max (admN n) ⌈adaptiveL c n * ((n:ℝ)+2)⌉₊ := by
      first | rfl | (unfold adaptiveN; rfl)
    rw [hNdef]
    push_cast
    apply max_le
    · linarith
    · have h4 : (0:ℝ) ≤ ((n:ℝ)+2)^4 := by positivity
      linarith
  have hcube8 : (8:ℝ) ≤ ((n:ℝ)+2)^3 := by
    nlinarith [hx, sq_nonneg ((n:ℝ)+2-2), sq_nonneg ((n:ℝ)+2),
      mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg ((n:ℝ)+2-2))]
  have h8 : (8:ℝ) ≤ adaptiveL c n := le_trans hcube8 hLx
  have h1 : ((n:ℝ)+2)^4 ≤ adaptiveL c n * ((n:ℝ)+2) := by
    have h := mul_le_mul_of_nonneg_right hLx hxpos.le
    calc ((n:ℝ)+2)^4 = ((n:ℝ)+2)^3 * ((n:ℝ)+2) := by ring
      _ ≤ adaptiveL c n * ((n:ℝ)+2) := h
  have h2 : (1:ℝ) ≤ adaptiveL c n * ((n:ℝ)+2) := by nlinarith [h8, hx]
  have hN3 : (adaptiveN c n : ℝ) ≤ 3 * (adaptiveL c n * ((n:ℝ)+2)) := by
    linarith [hNle, h1, h2]
  have hLHS : 1 / (2 * adaptiveL c n) *
      (C₀ * (C₀ ^ 2 * adaptiveL c n *
        ((adaptiveN c n : ℝ) * ((2 / adaptiveL c n) * S1mass (admR n)) ^ 2)))
      = 2 * C₀ ^ 3 * ((adaptiveN c n : ℝ) * S1mass (admR n) ^ 2)
          / adaptiveL c n ^ 2 := by
    first
      | (field_simp; ring)
      | (field_simp [hLne]; ring)
      | (field_simp [hLne])
  rw [hLHS]
  have hNnn : (0:ℝ) ≤ (adaptiveN c n : ℝ) := Nat.cast_nonneg _
  have hS1sq : S1mass (admR n) ^ 2 ≤ 16 * ((n:ℝ)+2)^2 := by
    have h := mul_self_le_mul_self hS1nn hS1
    calc S1mass (admR n) ^ 2
        = S1mass (admR n) * S1mass (admR n) := by ring
      _ ≤ (4 * ((n:ℝ)+2)) * (4 * ((n:ℝ)+2)) := h
      _ = 16 * ((n:ℝ)+2)^2 := by ring
  have hnum : (adaptiveN c n : ℝ) * S1mass (admR n) ^ 2
      ≤ 48 * (adaptiveL c n * ((n:ℝ)+2)^3) := by
    calc (adaptiveN c n : ℝ) * S1mass (admR n) ^ 2
        ≤ (3 * (adaptiveL c n * ((n:ℝ)+2))) * (16 * ((n:ℝ)+2)^2) := by
          apply mul_le_mul hN3 hS1sq (sq_nonneg _) (by positivity)
      _ = 48 * (adaptiveL c n * ((n:ℝ)+2)^3) := by ring
  have hden : adaptiveL c n * ((n:ℝ)+2)^3 ≤ adaptiveL c n ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hLx hLad.le
    calc adaptiveL c n * ((n:ℝ)+2)^3
        ≤ adaptiveL c n * adaptiveL c n := h
      _ = adaptiveL c n ^ 2 := by ring
  have hfrac : (adaptiveN c n : ℝ) * S1mass (admR n) ^ 2 / adaptiveL c n ^ 2
      ≤ 73 := by
    rw [div_le_iff₀ (pow_pos hLad 2)]
    linarith [hnum, hden, sq_nonneg (adaptiveL c n)]
  calc 2 * C₀ ^ 3 * ((adaptiveN c n : ℝ) * S1mass (admR n) ^ 2)
        / adaptiveL c n ^ 2
      = 2 * C₀ ^ 3 * ((adaptiveN c n : ℝ) * S1mass (admR n) ^ 2
          / adaptiveL c n ^ 2) := by ring
    _ ≤ 2 * C₀ ^ 3 * 73 := by
        apply mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = C₀ ^ 3 * 146 := by ring

/-- **BRICK 2b-ii (hShort O2 half, DONE at this theorem).** Uniform
boundedness of the decoded second-resolvent residual on Ω-compacts:
`‖O2res‖ ≤ C₀³·146` with `C₀` from `inv_norm_le_on_compact`, via the
δ := 1/C₀ reciprocal trick — no new gap provider. -/
theorem decodedSecondResolventResidual_uniform_bound (c : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), ∀ s ∈ K,
      ‖decodedAdaptiveSecondResolventResidual c n s‖ ≤ C := by
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := exists_uniform_lower_bound_on_compact K hK hKO
  obtain ⟨C₀, hC₀pos, hC₀⟩ := inv_norm_le_on_compact K hK hKO
  refine ⟨C₀ ^ 3 * 146,
    mul_pos (pow_pos hC₀pos 3) (by norm_num), fun n s hs => ?_⟩
  -- eigenvalues are nonnegative (decoded floor, banked)
  have heig : ∀ i, 0 ≤ decodedAdaptivePerturbedLam c n i := by
    intro i
    unfold decodedAdaptivePerturbedLam
    first
      | exact decodedEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n) _ _
          (fun k => galerkinFreeMu_nonneg _ _ k) i
      | exact decodedEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n)
          (fun k => galerkinFreeMu_nonneg _ _ k) i
      | (refine decodedEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n) _ _
            (fun k => ?_) i
         first
           | exact galerkinFreeMu_nonneg _ _ k
           | (unfold galerkinFreeMu; positivity)
           | exact sq_nonneg _)
      | exact decodedEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n) i
      | exact decodedEigenvalue_nonneg (adaptiveL c n) (adaptiveL_pos c n) _ i
  -- shifted-point resolvent bound for all lam ≥ 0 (textual clone of raw hbound')
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
  -- eigenvalue floor at δ := 1/C₀, the reciprocal trick
  have hlow : ∀ i, 1 / C₀ ≤ ‖s + (SupVConst : ℂ)
      + ((decodedAdaptivePerturbedLam c n i : ℝ) : ℂ)‖ := by
    intro i
    set z : ℂ := s + (SupVConst : ℂ)
        + ((decodedAdaptivePerturbedLam c n i : ℝ) : ℂ) with hz
    -- positive norm floor from the compact provider
    have hzfloor : δ₀ ≤ ‖z‖ := by
      have hnn : (0:ℝ) ≤ SupVConst + decodedAdaptivePerturbedLam c n i :=
        add_nonneg SupVConst_nonneg_adm (heig i)
      have h := hδ₀ s hs (SupVConst + decodedAdaptivePerturbedLam c n i) hnn
      have hcast : s + ((SupVConst + decodedAdaptivePerturbedLam c n i : ℝ) : ℂ)
          = z := by
        rw [hz]; push_cast; ring
      rw [hcast] at h
      exact h
    have hzpos : (0:ℝ) < ‖z‖ := lt_of_lt_of_le hδ₀pos hzfloor
    -- ‖z‖⁻¹ ≤ C₀ from the resolvent bound
    have hinvle : ‖z‖⁻¹ ≤ C₀ := by
      have h1 := hbound' (decodedAdaptivePerturbedLam c n i) (heig i)
      rw [← hz] at h1
      rw [norm_inv] at h1
      have hle1 : (1 + decodedAdaptivePerturbedLam c n i)⁻¹ ≤ 1 := by
        have h11 : (1:ℝ) ≤ 1 + decodedAdaptivePerturbedLam c n i := by
          have := heig i; linarith
        first
          | exact inv_le_one_of_one_le₀ h11
          | exact inv_le_one h11
          | (have h2 := one_div_le_one_div_of_le one_pos h11
             simpa [one_div] using h2)
      calc ‖z‖⁻¹ ≤ C₀ * (1 + decodedAdaptivePerturbedLam c n i)⁻¹ := h1
        _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hle1 hC₀pos.le
        _ = C₀ := mul_one C₀
    -- conclude 1/C₀ ≤ ‖z‖
    have hone : (1:ℝ) ≤ ‖z‖ * C₀ := by
      have h2 := mul_le_mul_of_nonneg_left hinvle (norm_nonneg z)
      rw [mul_inv_cancel₀ (ne_of_gt hzpos)] at h2
      exact h2
    rw [div_le_iff₀ hC₀pos]
    exact hone
  -- apply the banked master bound at δ := 1/C₀ and collapse
  have hδpos : (0:ℝ) < 1 / C₀ := by positivity
  have hmain := decodedSecondResolventResidual_norm_le c n s hδpos hC₀pos.le
      hlow hbound'
  have hinv : (1 / C₀)⁻¹ = C₀ := by rw [one_div, inv_inv]
  rw [hinv] at hmain
  exact le_trans hmain (decoded_residual_schedule_collapse c n hC₀pos)

#print axioms decodedSecondResolventResidual_norm_le
#print axioms decoded_residual_schedule_collapse
#print axioms decodedSecondResolventResidual_uniform_bound

end

end RHFormalization
