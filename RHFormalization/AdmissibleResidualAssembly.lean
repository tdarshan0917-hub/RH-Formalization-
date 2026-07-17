import RHFormalization.AdmissiblePrimeFirstOrderSplit
import RHFormalization.AdmissiblePrimeStageIdentity
import RHFormalization.AdmissibleWeightedColumnBound
import RHFormalization.AdmissibleResolventWeightSum
import RHFormalization.AdmissibleColumnNormBound
import RHFormalization.AdmissibleS1MassBound

/-!
# Brick 4b-iv (pointwise master bound)

Assembly of the Session-8 estimate bricks through the banked
weighted-column trace bound (4b-ii):

`‖SecondResolventResidual n s‖ ≤ (1/(2L)) · δ⁻¹ · (C₀²·L) · N·((2/L)·S₁(R))²`

at the schedule this is `~ N·S₁²/L² ~ 1/(n+2)`.  The hypotheses `hlow`
(eigenvalue floor at the shifted point) and `hbound` (resolvent-weight
bound at the shifted point) are discharged K-uniformly in the follow-up
brick (4b-iv, uniform form) via `inv_norm_le_on_compact` and
`admissibleEigenvalue_nonneg`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

open scoped BigOperators Classical

/-- **BRICK 4b-iv, pointwise master bound.** The density-normalized
second-resolvent residual at stage `n` is controlled by
`(1/(2L)) · δ⁻¹ · (C₀²L) · N·((2/L)S₁)²`. -/
theorem SecondResolventResidual_norm_le
    (n : ℕ) (s : ℂ) {δ C₀ : ℝ} (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (hlow : ∀ i, δ ≤ ‖s + (SupVConst : ℂ)
        + ((admPerturbedLam n i : ℝ) : ℂ)‖)
    (hbound : ∀ lam : ℝ, 0 ≤ lam →
        ‖(s + (SupVConst : ℂ) + (lam : ℂ))⁻¹‖ ≤ C₀ * (1 + lam)⁻¹) :
    ‖SecondResolventResidual n s‖
      ≤ 1 / (2 * admL n) *
          (δ⁻¹ * (C₀ ^ 2 * admL n *
            ((admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2))) := by
  classical
  have hL : (0 : ℝ) < admL n := admL_pos n
  have h2L : (0 : ℝ) < 2 * admL n := mul_pos (by norm_num) hL
  -- the eigenvalue-floor hypothesis in raw `perturbedEigenvalues` form
  have hlow' : ∀ i : Fin (admN n), δ ≤ ‖s + (SupVConst : ℂ)
      + ((perturbedEigenvalues (galerkinFreeMu (admN n) (admL n))
            (galerkinVC_isHermitian (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (admL n)) i : ℝ) : ℂ)‖ := by
    intro i
    have h := hlow i
    first
      | exact h
      | (unfold admPerturbedLam at h; exact h)
      | simpa [admPerturbedLam] using h
  -- BRICK 4b-ii at the shifted point
  have htr := trace_RD_V_RH_V_RD_norm_le_weighted_columns
      (galerkinFreeMu (admN n) (admL n))
      (galerkinVC_isHermitian (N := admN n) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
      (s + (SupVConst : ℂ)) hδ hlow'
  -- BRICK 4b-iii(b): uniform column bound
  have hcol : ∀ m : Fin (admN n),
      ‖Matrix.toEuclideanLin
          (galerkinVC (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (admL n)) (stdBasisE (admN n) m)‖ ^ 2
        ≤ (admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2 :=
    fun m => galerkinVC_column_norm_sq_le (admR n) (admL n) hL m
  -- BRICK 4b-iii(a) at the shifted point
  have hwsum := freeMu_resolvent_sq_sum_le (admN n) (admL n) hL
      (s + (SupVConst : ℂ)) C₀ hC₀ hbound
  have hB0 : (0 : ℝ)
      ≤ (admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2 := by
    positivity
  -- combine: Σ (weight² · column²) ≤ (C₀²L) · N((2/L)S₁)²
  have hsum :
      ∑ m : Fin (admN n),
        ‖(s + (SupVConst : ℂ)
            + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹‖ ^ 2
          * ‖Matrix.toEuclideanLin
              (galerkinVC (N := admN n) 1
                (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                (admL n)) (stdBasisE (admN n) m)‖ ^ 2
        ≤ C₀ ^ 2 * admL n
            * ((admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2) := by
    have h1 :
        ∑ m : Fin (admN n),
          ‖(s + (SupVConst : ℂ)
              + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹‖ ^ 2
            * ‖Matrix.toEuclideanLin
                (galerkinVC (N := admN n) 1
                  (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                  (admL n)) (stdBasisE (admN n) m)‖ ^ 2
          ≤ ∑ m : Fin (admN n),
              ‖(s + (SupVConst : ℂ)
                  + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹‖ ^ 2
                * ((admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2) :=
      Finset.sum_le_sum fun m _ =>
        mul_le_mul_of_nonneg_left (hcol m) (sq_nonneg _)
    have h2 :
        ∑ m : Fin (admN n),
          ‖(s + (SupVConst : ℂ)
              + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹‖ ^ 2
            * ((admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2)
          = (∑ m : Fin (admN n),
              ‖(s + (SupVConst : ℂ)
                  + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹‖ ^ 2)
              * ((admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2) := by
      first
        | rw [Finset.sum_mul]
        | rw [← Finset.sum_mul]
    have h3 :
        (∑ m : Fin (admN n),
            ‖(s + (SupVConst : ℂ)
                + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹‖ ^ 2)
            * ((admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2)
          ≤ C₀ ^ 2 * admL n
              * ((admN n : ℝ) * ((2 / admL n) * S1mass (admR n)) ^ 2) :=
      mul_le_mul_of_nonneg_right hwsum hB0
    exact le_trans h1 (le_trans (le_of_eq h2) h3)
  -- density-constant norm
  have hdens : ‖admDensityC n‖ = 1 / (2 * admL n) := by
    unfold admDensityC
    first
      | rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr h2L)]
      | rw [Complex.norm_ofReal, abs_of_pos (one_div_pos.mpr h2L)]
  -- assemble
  unfold SecondResolventResidual
  rw [norm_mul, hdens]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.mpr h2L))
  exact le_trans htr
    (mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hδ)))

#print axioms SecondResolventResidual_norm_le

end

end RHFormalization
