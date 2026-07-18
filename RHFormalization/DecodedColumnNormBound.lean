-- SENTINEL: decoded-column-norm-v1
import RHFormalization.DecodedVEntryBound
import RHFormalization.DecodedGalerkinFStageForwardGate
import Mathlib

/-!
# DecodedColumnNormBound — brick 1b of hShort
Column-norm bound for the DECODED potential matrix, cloning the raw
`galerkinVC_column_norm_sq_le` with the banked decoded entry bound.
Entry chain: |V^dec_{mn}| ≤ Σ|w| = S1mass (decoded bound is bumpMass-free,
so the same S1 constant works with room to spare).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real MeasureTheory
open scoped Real BigOperators

variable {N : ℕ}

/-- Entry-level S1 bound for the decoded normalized matrix. -/
theorem abs_decodedGalerkinV_entry_le_S1
    (R L : ℝ) (hL : 0 < L) (j m : Fin N) :
    |decodedGalerkinV (N := N) 1 (activePrimePowerCodesCenterBelow R)
        ppWeightReal L j m| ≤ (2 / L) * S1mass R := by
  show |(2 / L) * decodedVmatrixElement 1 (activePrimePowerCodesCenterBelow R)
      ppWeightReal L ((j : ℕ) + 1) ((m : ℕ) + 1)| ≤ (2 / L) * S1mass R
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 / L)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (abs_decodedVmatrixElement_le
    (activePrimePowerCodesCenterBelow R) ppWeightReal L hL.le _ _) ?_
  have hcong : ∀ q ∈ activePrimePowerCodesCenterBelow R,
      |ppWeightReal q| = ppWeightReal q :=
    fun q _ => abs_of_nonneg (ppWeightReal_nonneg q)
  rw [Finset.sum_congr rfl hcong]
  first
    | exact le_of_eq rfl
    | (show S1mass R ≤ S1mass R; exact le_rfl)
    | exact le_rfl

/-- **Decoded column-norm bound**: each column of the complexified decoded
matrix has norm² at most `N·((2/L)·S₁(R))²`. -/
theorem decodedGalerkinVC_column_norm_sq_le
    (R L : ℝ) (hL : 0 < L) (m : Fin N) :
    ‖Matrix.toEuclideanLin
        (decodedGalerkinVC (N := N) 1 (activePrimePowerCodesCenterBelow R)
          ppWeightReal L) (stdBasisE N m)‖ ^ 2
      ≤ (N : ℝ) * ((2 / L) * S1mass R) ^ 2 := by
  classical
  set V := decodedGalerkinVC (N := N) 1 (activePrimePowerCodesCenterBelow R)
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
    show ‖((decodedGalerkinV (N := N) 1 (activePrimePowerCodesCenterBelow R)
        ppWeightReal L j m : ℝ) : ℂ)‖ ≤ (2 / L) * S1mass R
    rw [Complex.norm_real]
    exact abs_decodedGalerkinV_entry_le_S1 R L hL j m
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

#print axioms abs_decodedGalerkinV_entry_le_S1
#print axioms decodedGalerkinVC_column_norm_sq_le

end

end RHFormalization
