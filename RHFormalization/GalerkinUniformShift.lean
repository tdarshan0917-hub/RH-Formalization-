/-
GalerkinUniformShift.lean

THE UNIFORM SHIFT (Proposition A/B.UNIFORM-LOWER-BOUND, operator level).
M := SupVConst makes H0 + galerkinV + M*I nonnegative at EVERY stage.
Proof idioms mirror the banked freeDiagOp_form_eq_sum / nonneg-discharge
files exactly (show-mulVec coordinate access, map_sum on RCLike.re,
normSq_eq_norm_sq).
-/
import RHFormalization.GalerkinFormBound
import RHFormalization.GalerkinStageSequence

namespace RHFormalization
noncomputable section
open Real Matrix

variable {N : ℕ}

/-- Real part of the complexified real-matrix form splits into the real
forms of the real and imaginary parts. -/
theorem re_form_complexified (A : Matrix (Fin N) (Fin N) ℝ)
    (y : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ y (pertOp (fun i j => ((A i j : ℝ) : ℂ)) y))
      = (∑ n : Fin N, ∑ m : Fin N, (y n).re * A n m * (y m).re)
        + (∑ n : Fin N, ∑ m : Fin N, (y n).im * A n m * (y m).im) := by
  unfold pertOp
  rw [PiLp.inner_apply, map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have happ : (Matrix.toEuclideanLin (fun i j => ((A i j : ℝ) : ℂ)) y) n
      = ∑ m : Fin N, ((A n m : ℝ) : ℂ) * y m := by
    show ((fun i j => ((A i j : ℝ) : ℂ)) *ᵥ (y : Fin N → ℂ)) n
        = ∑ m : Fin N, ((A n m : ℝ) : ℂ) * y m
    first
      | simp [Matrix.mulVec, dotProduct]
      | rfl
  rw [happ]
  rw [show inner ℂ (y n) (∑ m : Fin N, ((A n m : ℝ) : ℂ) * y m)
      = ∑ m : Fin N, (starRingEnd ℂ) (y n) * (((A n m : ℝ) : ℂ) * y m) by
    first
      | { rw [inner_sum]
          apply Finset.sum_congr rfl
          intro m _
          rw [RCLike.inner_apply] }
      | { rw [RCLike.inner_apply, Finset.mul_sum] }
      | { simp only [RCLike.inner_apply]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m _
          ring }]
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hz : ∀ z : ℂ, RCLike.re z = z.re := by
    intro z
    first
      | rfl
      | exact RCLike.re_to_complex
      | simp
  rw [hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Uniform complex form bound.** -/
theorem galerkinVC_re_form_bound (qs : Finset ℕ)
    (y : EuclideanSpace ℂ (Fin N)) :
    |RCLike.re (inner ℂ y (pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) y))|
      ≤ SupVConst * ‖y‖ ^ 2 := by
  have hVC : galerkinVC (N := N) 1 qs ppWeightReal 1
      = fun i j => ((galerkinV (N := N) 1 qs ppWeightReal 1 i j : ℝ) : ℂ) := rfl
  rw [hVC, re_form_complexified]
  have hre := galerkinV_form_bound (N := N) qs (fun n => (y n).re)
  have him := galerkinV_form_bound (N := N) qs (fun n => (y n).im)
  have hb1 : |∑ n : Fin N, ∑ m : Fin N,
      (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re|
      ≤ SupVConst * ∑ n : Fin N, ((y n).re) ^ 2 := by
    calc |∑ n : Fin N, ∑ m : Fin N,
          (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re|
        = |∑ n : Fin N, ∑ m : Fin N,
            (y n).re * (y m).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m| := by
          congr 1
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          ring
      _ ≤ SupVConst * ∑ n : Fin N, ((y n).re) ^ 2 := hre
  have hb2 : |∑ n : Fin N, ∑ m : Fin N,
      (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im|
      ≤ SupVConst * ∑ n : Fin N, ((y n).im) ^ 2 := by
    calc |∑ n : Fin N, ∑ m : Fin N,
          (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im|
        = |∑ n : Fin N, ∑ m : Fin N,
            (y n).im * (y m).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m| := by
          congr 1
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          ring
      _ ≤ SupVConst * ∑ n : Fin N, ((y n).im) ^ 2 := him
  have hnorm : ‖y‖ ^ 2 = (∑ n : Fin N, ((y n).re) ^ 2)
      + ∑ n : Fin N, ((y n).im) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have htri : |(∑ n : Fin N, ∑ m : Fin N,
      (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re)
      + ∑ n : Fin N, ∑ m : Fin N,
        (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im|
      ≤ |∑ n : Fin N, ∑ m : Fin N,
          (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re|
        + |∑ n : Fin N, ∑ m : Fin N,
          (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im| := by
    first
      | exact abs_add _ _
      | exact abs_add_le _ _
      | exact norm_add_le _ _
  calc |(∑ n : Fin N, ∑ m : Fin N,
        (y n).re * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).re)
        + ∑ n : Fin N, ∑ m : Fin N,
          (y n).im * galerkinV (N := N) 1 qs ppWeightReal 1 n m * (y m).im|
      ≤ _ + _ := htri
    _ ≤ SupVConst * (∑ n : Fin N, ((y n).re) ^ 2)
        + SupVConst * (∑ n : Fin N, ((y n).im) ^ 2) := add_le_add hb1 hb2
    _ = SupVConst * ‖y‖ ^ 2 := by rw [hnorm]; ring

/-- **THE UNIFORM SHIFT.** M = SupVConst works at every dimension and code set. -/
theorem galerkinOpCLM_nonneg_uniform
    (qs : Finset ℕ) (μ : Fin N → ℝ) (hμ : ∀ k, 0 ≤ μ k) :
    ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y
        (galerkinOpCLM μ 1 qs ppWeightReal 1 SupVConst y)) := by
  intro y
  rw [galerkinOpCLM_form_split]
  have happ2 : perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal 1) y
      = freeDiagOp μ y + pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) y := by
    rw [perturbedOp_eq_add]
    first
      | rfl
      | exact LinearMap.add_apply _ _ _
  rw [happ2, inner_add_right, _root_.map_add]
  have hfree : 0 ≤ RCLike.re (inner ℂ y (freeDiagOp μ y)) := by
    rw [freeDiagOp_form_eq_sum]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (sq_nonneg _)
  have hpert := galerkinVC_re_form_bound (N := N) qs y
  have habs := abs_le.mp hpert
  linarith [habs.1]

/-- galerkinFreeMu is nonnegative. -/
theorem galerkinFreeMu_nonneg (N : ℕ) (L : ℝ) (k : Fin N) :
    0 ≤ galerkinFreeMu N L k := by
  unfold galerkinFreeMu
  positivity

/-- **The uniformly-shifted genuine stage exhaustion** — the manuscript's
globally shifted finite-window family, in Lean. -/
def galerkinStageSeqU (n : ℕ) : DFiniteStage :=
  galerkinOperatorDFiniteStage (N := n + 1) n
    (galerkinFreeMu (n + 1) 1)
    1
    (activePrimePowerCodesCenterBelow ((n : ℝ) + 1))
    ppWeightReal
    1
    SupVConst
    (galerkinOpCLM_nonneg_uniform _ _ (fun k => galerkinFreeMu_nonneg _ _ k))

theorem galerkinStageSeqU_R (n : ℕ) :
    (galerkinStageSeqU n).R = (n : ℝ) + 1 := rfl

#print axioms re_form_complexified
#print axioms galerkinVC_re_form_bound
#print axioms galerkinOpCLM_nonneg_uniform
#print axioms galerkinStageSeqU

end
end RHFormalization
