import RHFormalization.DirichletEigenfunL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# RHFormalization.DirichletEigenfunInner
**Brick 3, stone 2.** Bridge the L²[0,L] inner product of the eigenfunctions
to the set integral of their product, and thence (with `hL`) to `∫ x in 0..L`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory Real
open scoped Real

/-- The L² element of the `n`-th eigenfunction. -/
noncomputable def eigenLp (n : ℕ) (L : ℝ) : (ℝ →₂[intervalMeasure L] ℝ) :=
  (memLp_dirichletEigenfun n L).toLp (dirichletEigenfun n L)

/-- The L² inner product equals the set integral of the product over the
interval measure. -/
theorem inner_eigenLp_eq_setIntegral (m n : ℕ) (L : ℝ) :
    inner ℝ (eigenLp m L) (eigenLp n L)
      = ∫ x, dirichletEigenfun m L x * dirichletEigenfun n L x
          ∂(intervalMeasure L) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hm := (memLp_dirichletEigenfun m L).coeFn_toLp
  have hn := (memLp_dirichletEigenfun n L).coeFn_toLp
  filter_upwards [hm, hn] with a ha hb
  simp only [eigenLp, ha, hb, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The set integral over the interval measure equals the interval integral
`∫ x in 0..L` (for `0 ≤ L`). -/
theorem setIntegral_intervalMeasure_eq (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : IntervalIntegrable f volume 0 L) :
    ∫ x, f x ∂(intervalMeasure L) = ∫ x in (0:ℝ)..L, f x := by
  rw [intervalIntegral.integral_of_le hL, intervalMeasure,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **Inner product of eigen-L² elements = interval integral of the product.** -/
theorem inner_eigenLp_eq_intervalIntegral (m n : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    inner ℝ (eigenLp m L) (eigenLp n L)
      = ∫ x in (0:ℝ)..L, dirichletEigenfun m L x * dirichletEigenfun n L x := by
  rw [inner_eigenLp_eq_setIntegral]
  apply setIntegral_intervalMeasure_eq _ L hL
  apply Continuous.intervalIntegrable
  exact (continuous_dirichletEigenfun m L).mul (continuous_dirichletEigenfun n L)

#print axioms eigenLp
#print axioms inner_eigenLp_eq_setIntegral
#print axioms inner_eigenLp_eq_intervalIntegral

end

end RHFormalization
