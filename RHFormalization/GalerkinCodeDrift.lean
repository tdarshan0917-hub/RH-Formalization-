/-
GalerkinCodeDrift.lean

CODE-DRIFT CONTROL (Lemma D.R->infty, matrix form): enlarging the code set
from qs to qs' moves every genuine galerkin eigenvalue by at most the
envelope tail sum over qs' \ qs. Chain: entrywise difference identity
(sdiff through the banked bump split), parametric form bound (the banked
Parseval chain with supV_tail_le in place of supV_uniform), parametric
complexification (mirror of galerkinVC_re_form_bound), Brick-10 Weyl.

The tail sum vanishes as qs exhausts (summable_weight_envelope), so this
is the second half -- with dimension monotonicity -- of the lambda_infty
existence argument for Front F.
-/
import RHFormalization.GalerkinWeylSupV
import RHFormalization.GalerkinCodeMono

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- The envelope tail constant of a code set. -/
def tailConst (qs : Finset ℕ) : ℝ :=
  ∑ q ∈ qs, |ppWeightReal q| * bumpEnvelope q

theorem tailConst_nonneg (qs : Finset ℕ) : 0 ≤ tailConst qs :=
  Finset.sum_nonneg fun q _ =>
    mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg _)

/-- Entrywise difference identity: for nested code sets, the difference of
bump matrices is the bump matrix of the set difference. -/
theorem galerkinV_sdiff (qs qs' : Finset ℕ) (hsub : qs ⊆ qs') (m n : Fin N) :
    galerkinV (N := N) 1 qs' ppWeightReal 1 m n
      - galerkinV (N := N) 1 qs ppWeightReal 1 m n
    = galerkinV (N := N) 1 (qs' \ qs) ppWeightReal 1 m n := by
  rw [galerkinV_apply, galerkinV_apply, galerkinV_apply,
    VmatrixElement_eq_sum_bumps, VmatrixElement_eq_sum_bumps,
    VmatrixElement_eq_sum_bumps]
  first
    | rw [eq_sub_iff_add_eq, Finset.sum_sdiff hsub]
    | (rw [Finset.sum_sdiff_eq_sub hsub]; ring)
    | (have h := Finset.sum_sdiff (f := fun q =>
          ppWeightReal q * bumpMatrixElement 1 q 1 ((m:ℕ)+1) ((n:ℕ)+1)) hsub
       linarith)

/-- **Parametric form bound**: the bump form over ANY code set is bounded
by that set's own envelope tail constant. Mirror of galerkinV_form_bound
with supV_tail_le in place of supV_uniform. -/
theorem galerkinV_form_bound_tail (qs : Finset ℕ) (a : Fin N → ℝ) :
    |∑ m : Fin N, ∑ n : Fin N, a m * a n * galerkinV (N := N) 1 qs ppWeightReal 1 m n|
      ≤ tailConst qs * ∑ m : Fin N, (a m) ^ 2 := by
  rw [galerkinV_form_eq_integral]
  have hcontf : Continuous (fun x =>
      primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2) :=
    (continuous_primePotentialFn_one qs).mul
      ((continuous_galerkinTrial a).pow 2)
  rw [show |2 * ∫ x in (0:ℝ)..1,
        primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2|
      = 2 * |∫ x in (0:ℝ)..1,
        primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2| from by
    rw [abs_mul]; norm_num]
  calc 2 * |∫ x in (0:ℝ)..1,
        primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2|
      ≤ 2 * ∫ x in (0:ℝ)..1,
          |primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2| := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have := intervalIntegral.norm_integral_le_integral_norm
          (f := fun x => primePotentialFn 1 qs ppWeightReal x
            * (galerkinTrial a x) ^ 2)
          (μ := MeasureTheory.volume) (by norm_num : (0:ℝ) ≤ 1)
        simpa using this
    _ ≤ 2 * ∫ x in (0:ℝ)..1, tailConst qs * (galerkinTrial a x) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact hcontf.abs.intervalIntegrable 0 1
        · exact (((continuous_galerkinTrial a).pow 2).const_mul
            (tailConst qs)).intervalIntegrable 0 1
        · intro x hx
          rw [abs_mul]
          rw [abs_of_nonneg (sq_nonneg (galerkinTrial a x))]
          refine mul_le_mul_of_nonneg_right (supV_tail_le qs ?_) (sq_nonneg _)
          first
            | exact hx
            | exact Set.mem_Icc.mpr ⟨hx.1, hx.2⟩
            | { rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
                exact hx }
    _ = 2 * (tailConst qs * ∫ x in (0:ℝ)..1, (galerkinTrial a x) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
    _ = 2 * (tailConst qs * ((∑ m : Fin N, (a m) ^ 2) / 2)) := by
        rw [galerkinTrial_normSq]
    _ = tailConst qs * ∑ m : Fin N, (a m) ^ 2 := by ring

/-- Parametric complex form bound: mirror of galerkinVC_re_form_bound. -/
theorem galerkinVC_re_form_bound_tail (qs : Finset ℕ)
    (y : EuclideanSpace ℂ (Fin N)) :
    |RCLike.re (inner ℂ y (pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) y))|
      ≤ tailConst qs * ‖y‖ ^ 2 := by
  have hVC : galerkinVC (N := N) 1 qs ppWeightReal 1
      = fun i j => ((galerkinV (N := N) 1 qs ppWeightReal 1 i j : ℝ) : ℂ) := rfl
  rw [hVC, re_form_complexified]
  have hre := galerkinV_form_bound_tail (N := N) qs (fun n => (y n).re)
  have him := galerkinV_form_bound_tail (N := N) qs (fun n => (y n).im)
  have hnorm : ‖y‖ ^ 2
      = (∑ n : Fin N, ((y n).re) ^ 2) + (∑ n : Fin N, ((y n).im) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    first
      | { rw [Complex.sq_abs] ; rw [Complex.normSq_apply] }
      | { rw [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply] }
      | { rw [Complex.normSq_eq_norm_sq.symm] ; rw [Complex.normSq_apply] }
      | { have h := Complex.normSq_apply (y i)
          rw [← Complex.normSq_eq_norm_sq, h]
          ring }
      | { rw [Complex.sq_abs (y i), Complex.normSq_apply] ; ring }
  have hb1 : |∑ n : Fin N, ∑ m : Fin N,
      (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re|
      ≤ tailConst qs * ∑ n : Fin N, ((y n).re) ^ 2 := by
    calc |∑ n : Fin N, ∑ m : Fin N,
        (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re|
        = |∑ n : Fin N, ∑ m : Fin N,
            (y n).re * (y m).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m| := by
          congr 1
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          ring
      _ ≤ tailConst qs * ∑ n : Fin N, ((y n).re) ^ 2 := hre
  have hb2 : |∑ n : Fin N, ∑ m : Fin N,
      (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im|
      ≤ tailConst qs * ∑ n : Fin N, ((y n).im) ^ 2 := by
    calc |∑ n : Fin N, ∑ m : Fin N,
        (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im|
        = |∑ n : Fin N, ∑ m : Fin N,
            (y n).im * (y m).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m| := by
          congr 1
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          ring
      _ ≤ tailConst qs * ∑ n : Fin N, ((y n).im) ^ 2 := him
  have htri : |(∑ n : Fin N, ∑ m : Fin N,
      (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re)
      + (∑ n : Fin N, ∑ m : Fin N,
        (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im)|
      ≤ |∑ n : Fin N, ∑ m : Fin N,
          (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re|
        + |∑ n : Fin N, ∑ m : Fin N,
            (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im| := by
    first
      | exact abs_add _ _
      | exact abs_add_le _ _
      | apply abs_add
      | exact norm_add_le
          (∑ n : Fin N, ∑ m : Fin N,
            (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re)
          (∑ n : Fin N, ∑ m : Fin N,
            (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im)
  calc |(∑ n : Fin N, ∑ m : Fin N,
      (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re)
      + (∑ n : Fin N, ∑ m : Fin N,
        (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im)|
      ≤ _ + _ := htri
    _ ≤ tailConst qs * (∑ n : Fin N, ((y n).re) ^ 2)
        + tailConst qs * (∑ n : Fin N, ((y n).im) ^ 2) := add_le_add hb1 hb2
    _ = tailConst qs * ‖y‖ ^ 2 := by rw [hnorm]; ring

/-- **CODE-DRIFT WEYL BOUND.** For nested code sets at fixed dimension,
every genuine eigenvalue moves by at most the envelope tail over the new
codes. -/
theorem galerkinEigenvalues_code_drift (qs qs' : Finset ℕ) (hsub : qs ⊆ qs')
    (μ : Fin N → ℝ) (k : Fin N) :
    |perturbedEigenvalues μ
        (galerkinVC_isHermitian (N := N) 1 qs' ppWeightReal 1) k
      - perturbedEigenvalues μ
          (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) k|
      ≤ tailConst (qs' \ qs) := by
  apply eigenvalues_dist_le
    (perturbedOp_isSymmetric μ (galerkinVC_isHermitian (N := N) 1 qs' ppWeightReal 1))
    (perturbedOp_isSymmetric μ (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1))
    perturbedOp_finrank
  intro x
  have hsplit' : perturbedOp μ (galerkinVC (N := N) 1 qs' ppWeightReal 1) x
      = freeDiagOp μ x + pertOp (galerkinVC (N := N) 1 qs' ppWeightReal 1) x := by
    rw [perturbedOp_eq_add]
    first
      | rfl
      | exact LinearMap.add_apply _ _ _
  have hsplit : perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal 1) x
      = freeDiagOp μ x + pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) x := by
    rw [perturbedOp_eq_add]
    first
      | rfl
      | exact LinearMap.add_apply _ _ _
  rw [hsplit', hsplit, inner_add_right, inner_add_right,
    _root_.map_add, _root_.map_add]
  have hdiff : RCLike.re (inner ℂ x
        (pertOp (galerkinVC (N := N) 1 qs' ppWeightReal 1) x))
      - RCLike.re (inner ℂ x
          (pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) x))
      = RCLike.re (inner ℂ x
          (pertOp (galerkinVC (N := N) 1 (qs' \ qs) ppWeightReal 1) x)) := by
    have hpert : pertOp (galerkinVC (N := N) 1 qs' ppWeightReal 1)
        = pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1)
          + pertOp (galerkinVC (N := N) 1 (qs' \ qs) ppWeightReal 1) := by
      unfold pertOp
      rw [← _root_.map_add]
      congr 1
      ext i j
      have h := galerkinV_sdiff (N := N) qs qs' hsub i j
      show (galerkinV (N := N) 1 qs' ppWeightReal 1 i j : ℂ)
          = ((galerkinV (N := N) 1 qs ppWeightReal 1 i j : ℝ) : ℂ)
            + ((galerkinV (N := N) 1 (qs' \ qs) ppWeightReal 1 i j : ℝ) : ℂ)
      rw [← Complex.ofReal_add]
      norm_cast
      linarith
    rw [hpert, LinearMap.add_apply, inner_add_right, _root_.map_add]
    ring
  have hgoal : RCLike.re (inner ℂ x (freeDiagOp μ x))
        + RCLike.re (inner ℂ x
          (pertOp (galerkinVC (N := N) 1 qs' ppWeightReal 1) x))
      - (RCLike.re (inner ℂ x (freeDiagOp μ x))
        + RCLike.re (inner ℂ x
          (pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) x)))
      = RCLike.re (inner ℂ x
          (pertOp (galerkinVC (N := N) 1 (qs' \ qs) ppWeightReal 1) x)) := by
    rw [← hdiff]; ring
  rw [hgoal]
  exact galerkinVC_re_form_bound_tail (qs' \ qs) x

#print axioms tailConst
#print axioms galerkinV_sdiff
#print axioms galerkinV_form_bound_tail
#print axioms galerkinVC_re_form_bound_tail
#print axioms galerkinEigenvalues_code_drift

end

end RHFormalization
