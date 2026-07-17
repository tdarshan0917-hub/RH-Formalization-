/-
GalerkinFormBound.lean

The manuscript's A/B.UNIFORM-LOWER-BOUND at the Galerkin matrix level (real
form). For the genuine bump matrix at (delta, L) = (1, 1) with arithmetic
weights: |sum_{m,n} a_m a_n V_{mn}| <= SupVConst * sum_m a_m^2, uniformly in
N and the code set. Route: bilinear expansion to the position-space integral
int V f^2, the sup-anchor pointwise, and Dirichlet-sine orthonormality.
-/
import RHFormalization.SupVBound
import RHFormalization.GalerkinMatrices
import RHFormalization.DirichletEigenfunONB
import RHFormalization.DirichletEigenfunOrthogonal

namespace RHFormalization
noncomputable section
open Real

variable {N : ℕ}

/-- The synthesized Galerkin trial function. -/
def galerkinTrial (a : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ m : Fin N, a m * dirichletEigenfun ((m : ℕ) + 1) 1 x

theorem continuous_galerkinTrial (a : Fin N → ℝ) :
    Continuous (galerkinTrial a) := by
  unfold galerkinTrial
  apply continuous_finset_sum
  intro m _
  exact (continuous_dirichletEigenfun _ 1).const_mul _

theorem continuous_primePotentialFn_one (qs : Finset ℕ) :
    Continuous (primePotentialFn 1 qs ppWeightReal) := by
  unfold primePotentialFn
  apply continuous_finset_sum
  intro q _
  unfold gaussBump
  fun_prop

/-- Bilinear expansion: the matrix form equals the position-space integral. -/
theorem galerkinV_form_eq_integral (qs : Finset ℕ) (a : Fin N → ℝ) :
    ∑ m : Fin N, ∑ n : Fin N, a m * a n * galerkinV (N := N) 1 qs ppWeightReal 1 m n
      = 2 * ∫ x in (0:ℝ)..1,
          primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2 := by
  have hint : ∀ (g : ℝ → ℝ), Continuous g →
      IntervalIntegrable g MeasureTheory.volume 0 1 :=
    fun g hg => hg.intervalIntegrable 0 1
  have hexp : ∀ x : ℝ,
      primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2
        = ∑ m : Fin N, ∑ n : Fin N,
            a m * a n * (dirichletEigenfun ((m:ℕ)+1) 1 x
              * primePotentialFn 1 qs ppWeightReal x
              * dirichletEigenfun ((n:ℕ)+1) 1 x) := by
    intro x
    unfold galerkinTrial
    rw [sq, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  calc ∑ m : Fin N, ∑ n : Fin N,
        a m * a n * galerkinV (N := N) 1 qs ppWeightReal 1 m n
      = 2 * ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * ∫ x in (0:ℝ)..1,
              dirichletEigenfun ((m:ℕ)+1) 1 x
                * primePotentialFn 1 qs ppWeightReal x
                * dirichletEigenfun ((n:ℕ)+1) 1 x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [galerkinV_apply]
        show a m * a n * (2 / 1 * VmatrixElement 1 qs ppWeightReal 1 (↑m + 1) (↑n + 1)) = _
        norm_num
        first
          | (rw [show VmatrixElement 1 qs ppWeightReal 1 (↑m + 1) (↑n + 1)
                = ∫ x in (0:ℝ)..1,
                    dirichletEigenfun ((m:ℕ)+1) 1 x
                      * primePotentialFn 1 qs ppWeightReal x
                      * dirichletEigenfun ((n:ℕ)+1) 1 x from rfl]
             ring)
          | (unfold VmatrixElement; ring)
    _ = 2 * ∑ m : Fin N, ∑ n : Fin N,
          ∫ x in (0:ℝ)..1, a m * a n
            * (dirichletEigenfun ((m:ℕ)+1) 1 x
              * primePotentialFn 1 qs ppWeightReal x
              * dirichletEigenfun ((n:ℕ)+1) 1 x) := by
        congr 1
        apply Finset.sum_congr rfl; intro m _
        apply Finset.sum_congr rfl; intro n _
        rw [intervalIntegral.integral_const_mul]
    _ = 2 * ∫ x in (0:ℝ)..1, ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * (dirichletEigenfun ((m:ℕ)+1) 1 x
            * primePotentialFn 1 qs ppWeightReal x
            * dirichletEigenfun ((n:ℕ)+1) 1 x) := by
        congr 1
        rw [intervalIntegral.integral_finset_sum]
        · apply Finset.sum_congr rfl; intro m _
          rw [intervalIntegral.integral_finset_sum]
          intro n _
          apply hint
          apply Continuous.const_mul
          exact ((continuous_dirichletEigenfun _ 1).mul
            (continuous_primePotentialFn_one qs)).mul
            (continuous_dirichletEigenfun _ 1)
        · intro m _
          apply hint
          apply continuous_finset_sum
          intro n _
          apply Continuous.const_mul
          exact ((continuous_dirichletEigenfun _ 1).mul
            (continuous_primePotentialFn_one qs)).mul
            (continuous_dirichletEigenfun _ 1)
    _ = 2 * ∫ x in (0:ℝ)..1,
          primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2 := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x _
        exact (hexp x).symm

/-- Parseval: the trial function's L2 norm-squared is the coefficient sum. -/
theorem galerkinTrial_normSq (a : Fin N → ℝ) :
    (∫ x in (0:ℝ)..1, (galerkinTrial a x) ^ 2) = (∑ m : Fin N, (a m) ^ 2) / 2 := by
  have hexp : ∀ x : ℝ, (galerkinTrial a x) ^ 2
      = ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * (dirichletEigenfun ((m:ℕ)+1) 1 x * dirichletEigenfun ((n:ℕ)+1) 1 x) := by
    intro x
    unfold galerkinTrial
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hcont2 : ∀ m n : ℕ, Continuous (fun x =>
      dirichletEigenfun m 1 x * dirichletEigenfun n 1 x) :=
    fun m n => (continuous_dirichletEigenfun m 1).mul
      (continuous_dirichletEigenfun n 1)
  calc (∫ x in (0:ℝ)..1, (galerkinTrial a x) ^ 2)
      = ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * ∫ x in (0:ℝ)..1,
              dirichletEigenfun ((m:ℕ)+1) 1 x * dirichletEigenfun ((n:ℕ)+1) 1 x := by
        rw [intervalIntegral.integral_congr
          (g := fun x => ∑ m : Fin N, ∑ n : Fin N, a m * a n
            * (dirichletEigenfun ((m:ℕ)+1) 1 x
              * dirichletEigenfun ((n:ℕ)+1) 1 x))
          (fun x _ => hexp x)]
        rw [intervalIntegral.integral_finset_sum]
        · apply Finset.sum_congr rfl; intro m _
          rw [intervalIntegral.integral_finset_sum]
          · apply Finset.sum_congr rfl; intro n _
            rw [intervalIntegral.integral_const_mul]
          · intro n _
            exact (((hcont2 _ _).const_mul _)).intervalIntegrable 0 1
        · intro m _
          apply Continuous.intervalIntegrable
          apply continuous_finset_sum
          intro n _
          exact ((hcont2 _ _).const_mul _)
    _ = ∑ m : Fin N, (a m) ^ 2 / 2 := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_eq_single m]
        · have h2 : (∫ x in (0:ℝ)..1,
              dirichletEigenfun ((m:ℕ)+1) 1 x * dirichletEigenfun ((m:ℕ)+1) 1 x)
              = 1 / 2 := by
            have hlem := integral_dirichletEigenfun_sq ((m:ℕ)+1) 1 one_pos
              (by omega)
            rw [show (1:ℝ)/2 = 1/2 from rfl, ← hlem]
            apply intervalIntegral.integral_congr
            intro x _
            simp only [sq]
          rw [h2]
          ring
        · intro n _ hnm
          rw [eigenfun_orthogonal ((m:ℕ)+1) ((n:ℕ)+1) 1 one_ne_zero
            (by
              intro h
              apply hnm
              have : (n : ℕ) = (m : ℕ) := by omega
              exact Fin.ext this)]
          ring
        · intro hm
          exact absurd (Finset.mem_univ m) hm
    _ = (∑ m : Fin N, (a m) ^ 2) / 2 := by
        rw [Finset.sum_div]

/-- **A/B.UNIFORM-LOWER-BOUND (matrix form).** The genuine bump form is
bounded by SupVConst times the coefficient norm, uniformly in N and qs. -/
theorem galerkinV_form_bound (qs : Finset ℕ) (a : Fin N → ℝ) :
    |∑ m : Fin N, ∑ n : Fin N, a m * a n * galerkinV (N := N) 1 qs ppWeightReal 1 m n|
      ≤ SupVConst * ∑ m : Fin N, (a m) ^ 2 := by
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
    _ ≤ 2 * ∫ x in (0:ℝ)..1, SupVConst * (galerkinTrial a x) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact hcontf.abs.intervalIntegrable 0 1
        · exact (((continuous_galerkinTrial a).pow 2).const_mul
            SupVConst).intervalIntegrable 0 1
        · intro x hx
          rw [abs_mul]
          rw [abs_of_nonneg (sq_nonneg (galerkinTrial a x))]
          refine mul_le_mul_of_nonneg_right (supV_uniform qs ?_) (sq_nonneg _)
          first
            | exact hx
            | exact Set.mem_Icc.mpr ⟨hx.1, hx.2⟩
            | { rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
                exact hx }
    _ = 2 * (SupVConst * ∫ x in (0:ℝ)..1, (galerkinTrial a x) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
    _ = 2 * (SupVConst * ((∑ m : Fin N, (a m) ^ 2) / 2)) := by
        rw [galerkinTrial_normSq]
    _ = SupVConst * ∑ m : Fin N, (a m) ^ 2 := by ring

#print axioms galerkinV_form_eq_integral
#print axioms galerkinTrial_normSq
#print axioms galerkinV_form_bound

end
end RHFormalization
