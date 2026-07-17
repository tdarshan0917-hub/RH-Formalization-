import Mathlib
import RHFormalization.GalerkinFormBound
import RHFormalization.SupVBound
import RHFormalization.DirichletEigenfunL2
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Real MeasureTheory

namespace RHFormalization

/-- **A.ENV-FORM (finite-N form bound on the genuine operator).** The genuine
prime-perturbation matrix form is bounded by the sup-anchor constant times the
box mass of the trial function:
`∑_{m,n} a_m a_n V_{mn} ≤ 2·SupVConst·∫₀¹ (trial a)²`.
Composes the banked bilinear-integral identity (`galerkinV_form_eq_integral`)
with the banked uniform sup-anchor (`supV_uniform`). Finite-N image of the
manuscript KLMN relative form bound, on the exact live operator with the frozen
√q weight `ppWeightReal`. Uniform in `qs` (the cutoff R). -/
theorem galerkinV_form_le_supV
    {N : ℕ} (qs : Finset ℕ) (a : Fin N → ℝ) :
    ∑ m : Fin N, ∑ n : Fin N, a m * a n * galerkinV (N := N) 1 qs ppWeightReal 1 m n
      ≤ 2 * SupVConst * ∫ x in (0:ℝ)..1, (galerkinTrial a x) ^ 2 := by
  rw [galerkinV_form_eq_integral qs a, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  have hcont_pot : Continuous (primePotentialFn 1 qs ppWeightReal) :=
    continuous_primePotentialFn_one qs
  have hcont_trial : Continuous (fun x => (galerkinTrial a x) ^ 2) := by
    have htrial : Continuous (galerkinTrial a) := by
      unfold galerkinTrial
      apply continuous_finsetSum
      intro i _
      exact (continuous_dirichletEigenfun ((i:ℕ)+1) 1).const_mul _
    exact htrial.pow 2
  have hptwise : ∀ x ∈ Set.Icc (0:ℝ) 1,
      primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2
        ≤ SupVConst * (galerkinTrial a x) ^ 2 := by
    intro x hx
    have hbound : primePotentialFn 1 qs ppWeightReal x ≤ SupVConst :=
      le_trans (le_abs_self _) (supV_uniform qs hx)
    exact mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
  have hint_le : ∫ x in (0:ℝ)..1, primePotentialFn 1 qs ppWeightReal x * (galerkinTrial a x) ^ 2
      ≤ ∫ x in (0:ℝ)..1, SupVConst * (galerkinTrial a x) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (hcont_pot.mul hcont_trial).intervalIntegrable 0 1
    · exact (continuous_const.mul hcont_trial).intervalIntegrable 0 1
    · intro x hx; exact hptwise x hx
  rw [intervalIntegral.integral_const_mul] at hint_le
  exact hint_le

#print axioms galerkinV_form_le_supV

end RHFormalization
