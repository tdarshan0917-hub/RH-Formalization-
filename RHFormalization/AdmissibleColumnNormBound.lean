import RHFormalization.GalerkinFStageForwardGate
import RHFormalization.VMatrixElementBound
import RHFormalization.AdmissibleS1MassBound
import RHFormalization.AdmissibleFreeResolventOp

/-!
# RHFormalization.AdmissibleColumnNormBound

**BRICK 4b-iii(b): the V column-norm bound.**

`‖(galerkinVC 1 qs ppWeightReal L) eₘ‖² ≤ N·((2/L)·S₁(R))²` for
`qs = activePrimePowerCodesCenterBelow R`.

Chain: unit bump mass (`bumpMass 1 q L ≤ 1`, monotone domination by the
full-line normalized Gaussian) → entry bound
`|galerkinV| ≤ (2/L)·S₁(R)` (weights nonneg, banked `abs_VmatrixElement_le`
+ `S1mass` def) → column sum of squares. Provable at `1/L`-scaling
PRECISELY because of the Session 8 normalization fix.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Real MeasureTheory
open scoped BigOperators Classical

variable {N : ℕ}

/-- Unit bump mass: `∫₀ᴸ gaussBump 1 (x − log q) dx ≤ 1` — the window
integral of the normalized Gaussian is at most its full-line mass 1. -/
theorem bumpMass_le_one (q : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    bumpMass 1 q L ≤ 1 := by
  unfold bumpMass
  have hpos : ∀ x : ℝ, 0 ≤ gaussBump 1 (x - Real.log q) := by
    intro x
    unfold gaussBump
    positivity
  have hInt : MeasureTheory.Integrable
      (fun x : ℝ => gaussBump 1 (x - Real.log q)) := by
    unfold gaussBump
    simp only [one_pow, mul_one]
    have h1 : MeasureTheory.Integrable (fun x : ℝ =>
        Real.exp (-(1/2 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    have h2 : MeasureTheory.Integrable (fun x : ℝ =>
        Real.exp (-(1/2 : ℝ) * (x - Real.log q) ^ 2)) := by
      first
        | exact h1.comp_sub_right (Real.log q)
        | exact (MeasureTheory.integrable_comp_sub_right
            (fun x => Real.exp (-(1/2 : ℝ) * x ^ 2)) (Real.log q)).mpr h1
    have h3 : MeasureTheory.Integrable (fun x : ℝ =>
        Real.exp (-(1/2 : ℝ) * (x - Real.log q) ^ 2)
          / Real.sqrt (2 * Real.pi)) := by
      first
        | · have h4 := h2.mul_const ((Real.sqrt (2 * Real.pi))⁻¹)
            refine h4.congr ?_
            filter_upwards with x
            rw [div_eq_mul_inv]
        | · have h4 := h2.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
            refine h4.congr ?_
            filter_upwards with x
            rw [div_eq_inv_mul]
        | · have h4 := h2.smul ((Real.sqrt (2 * Real.pi))⁻¹)
            refine h4.congr ?_
            filter_upwards with x
            simp only [Pi.smul_apply, smul_eq_mul]
            rw [div_eq_inv_mul]
        | exact h2.div_const _
    refine h3.congr ?_
    filter_upwards with x
    congr 1
    ring
  have hint_full : (∫ x : ℝ, gaussBump 1 (x - Real.log q)) = 1 := by
    unfold gaussBump
    simp only [one_pow, mul_one]
    have hshift : (∫ x : ℝ, Real.exp (-(x - Real.log q) ^ 2 / 2)
          / Real.sqrt (2 * Real.pi))
        = ∫ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
      first
        | exact MeasureTheory.integral_sub_right_eq_self
            (fun x => Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))
            (Real.log q)
        | · rw [← MeasureTheory.integral_sub_right_eq_self
              (fun x => Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))
              (Real.log q)]
    rw [hshift]
    have hgauss : (∫ x : ℝ, Real.exp (-(1/2 : ℝ) * x ^ 2))
        = Real.sqrt (Real.pi / (1/2 : ℝ)) := integral_gaussian (1/2 : ℝ)
    have hcongr : (∫ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))
        = (∫ x : ℝ, Real.exp (-(1/2 : ℝ) * x ^ 2)) / Real.sqrt (2 * Real.pi) := by
      rw [MeasureTheory.integral_div]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      congr 1
      ring
    rw [hcongr, hgauss,
      show Real.pi / (1/2 : ℝ) = 2 * Real.pi by ring]
    exact div_self (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)
  have hle_full : (∫ x in (0:ℝ)..L, gaussBump 1 (x - Real.log q))
      ≤ ∫ x : ℝ, gaussBump 1 (x - Real.log q) := by
    rw [intervalIntegral.integral_of_le hL]
    first
      | exact MeasureTheory.setIntegral_le_integral hInt
          (Filter.Eventually.of_forall hpos)
      | exact MeasureTheory.integral_mono_measure
          MeasureTheory.Measure.restrict_le_self
          (Filter.Eventually.of_forall hpos) hInt
  linarith

/-- **Entry bound at the slow cutoff**: every orthonormal-normalized entry is
at most `(2/L)·S₁(R)`. -/
theorem abs_galerkinV_entry_le_S1
    (R L : ℝ) (hL : 0 < L) (m n : Fin N) :
    |galerkinV (N := N) 1 (activePrimePowerCodesCenterBelow R) ppWeightReal L m n|
      ≤ (2 / L) * S1mass R := by
  rw [galerkinV_apply, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 / L)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |VmatrixElement 1 (activePrimePowerCodesCenterBelow R) ppWeightReal L
          ((m : ℕ) + 1) ((n : ℕ) + 1)|
      ≤ ∑ q ∈ activePrimePowerCodesCenterBelow R,
          |ppWeightReal q| * bumpMass 1 q L :=
        abs_VmatrixElement_le 1 one_pos _ ppWeightReal L hL.le _ _
    _ ≤ ∑ q ∈ activePrimePowerCodesCenterBelow R, ppWeightReal q := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_of_nonneg (ppWeightReal_nonneg q)]
        calc ppWeightReal q * bumpMass 1 q L
            ≤ ppWeightReal q * 1 :=
              mul_le_mul_of_nonneg_left (bumpMass_le_one q L hL.le)
                (ppWeightReal_nonneg q)
          _ = ppWeightReal q := mul_one _
    _ = S1mass R := rfl

/-- **BRICK 4b-iii(b): the column-norm bound.** Each column of the
complexified genuine bump matrix has norm² at most `N·((2/L)·S₁(R))²`. -/
theorem galerkinVC_column_norm_sq_le
    (R L : ℝ) (hL : 0 < L) (m : Fin N) :
    ‖Matrix.toEuclideanLin
        (galerkinVC (N := N) 1 (activePrimePowerCodesCenterBelow R)
          ppWeightReal L) (stdBasisE N m)‖ ^ 2
      ≤ (N : ℝ) * ((2 / L) * S1mass R) ^ 2 := by
  classical
  set V := galerkinVC (N := N) 1 (activePrimePowerCodesCenterBelow R)
    ppWeightReal L with hV
  set v := Matrix.toEuclideanLin V (stdBasisE N m) with hv
  have hnorm : ‖v‖ = Real.sqrt (∑ j : Fin N, ‖v j‖ ^ 2) := by
    first
      | exact EuclideanSpace.norm_eq v
      | exact PiLp.norm_eq_of_L2 _ v
  have hsq : ‖v‖ ^ 2 = ∑ j : Fin N, ‖v.ofLp j‖ ^ 2 := by
    first
      | (rw [hnorm]
         exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _))
      | (rw [hnorm]
         rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)])
      | (rw [hnorm]
         rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
         rfl)
  rw [hsq]
  have hcoord : ∀ j : Fin N, v.ofLp j = V j m := by
    intro j
    rw [hv]
    simp [stdBasisE, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.basisFun, PiLp.single_apply, Finset.sum_ite_eq,
      mul_comm]
    have hw : ((LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ (Fin N))).symm
          (EuclideanSpace.single m (1 : ℂ)))
        = EuclideanSpace.single m (1 : ℂ) := by
      first
        | rfl
        | simp [LinearIsometryEquiv.refl_symm]
        | simp
    rw [hw]
    refine (Finset.sum_eq_single m ?_ ?_).trans ?_
    · intro b _ hbm
      have hb0 : (EuclideanSpace.single m (1 : ℂ)).ofLp b = 0 := by
        first
          | (rw [PiLp.single_apply]
             exact if_neg hbm)
          | (rw [EuclideanSpace.single_apply]
             exact if_neg hbm)
          | exact Pi.single_eq_of_ne hbm (1 : ℂ)
          | exact Pi.single_eq_of_ne (Ne.symm hbm) (1 : ℂ)
          | simp [PiLp.single_apply, hbm]
          | simp [EuclideanSpace.single_apply, hbm]
          | simp [EuclideanSpace.single, hbm]
          | simp [hbm]
      rw [hb0, mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
    · have hb1 : (EuclideanSpace.single m (1 : ℂ)).ofLp m = 1 := by
        first
          | (rw [PiLp.single_apply]
             exact if_pos rfl)
          | (rw [EuclideanSpace.single_apply]
             exact if_pos rfl)
          | exact Pi.single_eq_same m (1 : ℂ)
          | simp [PiLp.single_apply]
          | simp [EuclideanSpace.single_apply]
          | simp [EuclideanSpace.single]
          | simp
      rw [hb1, mul_one]
  have hentry : ∀ j : Fin N, ‖v.ofLp j‖ ≤ (2 / L) * S1mass R := by
    intro j
    rw [hcoord j, hV]
    show ‖((galerkinV (N := N) 1 (activePrimePowerCodesCenterBelow R)
        ppWeightReal L j m : ℝ) : ℂ)‖ ≤ (2 / L) * S1mass R
    rw [Complex.norm_real]
    exact abs_galerkinV_entry_le_S1 R L hL j m
  calc ∑ j : Fin N, ‖v.ofLp j‖ ^ 2
      ≤ ∑ _j : Fin N, ((2 / L) * S1mass R) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := hentry j
        have hn : (0:ℝ) ≤ ‖v.ofLp j‖ := norm_nonneg _
        nlinarith
    _ = (N : ℝ) * ((2 / L) * S1mass R) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

#print axioms bumpMass_le_one
#print axioms abs_galerkinV_entry_le_S1
#print axioms galerkinVC_column_norm_sq_le

end

end RHFormalization
