import RHFormalization.PrimePotentialPosition

/-!
# Brick 2, stone 2: single-bump decomposition `V_{mn} = ∑_q w(q)·B_{mn}(q)`.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real MeasureTheory intervalIntegral
open scoped Real

/-- Single-bump matrix element. -/
noncomputable def bumpMatrixElement
    (δ : ℝ) (q : ℕ) (L : ℝ) (m n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..L,
    dirichletEigenfun m L x * gaussBump δ (x - Real.log q) * dirichletEigenfun n L x

theorem continuous_summand (δ : ℝ) (q : ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) :
    Continuous (fun x : ℝ =>
      w q * (dirichletEigenfun m L x * gaussBump δ (x - Real.log q) * dirichletEigenfun n L x)) := by
  unfold dirichletEigenfun gaussBump
  fun_prop

theorem integrand_sum_eq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) (x : ℝ) :
    dirichletEigenfun m L x * (∑ q ∈ qs, w q * gaussBump δ (x - Real.log q))
        * dirichletEigenfun n L x
      = ∑ q ∈ qs,
          w q * (dirichletEigenfun m L x * gaussBump δ (x - Real.log q)
                  * dirichletEigenfun n L x) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem VmatrixElement_eq_sum_bumps
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) :
    VmatrixElement δ qs w L m n
      = ∑ q ∈ qs, w q * bumpMatrixElement δ q L m n := by
  unfold VmatrixElement primePotentialFn
  rw [intervalIntegral.integral_congr
        (g := fun x =>
          ∑ q ∈ qs, w q * (dirichletEigenfun m L x * gaussBump δ (x - Real.log q)
                            * dirichletEigenfun n L x))
        (fun x _ => integrand_sum_eq δ qs w L m n x)]
  rw [intervalIntegral.integral_finsetSum
        (fun q _ => (continuous_summand δ q w L m n).intervalIntegrable 0 L)]
  apply Finset.sum_congr rfl
  intro q _
  unfold bumpMatrixElement
  rw [intervalIntegral.integral_const_mul]

#print axioms VmatrixElement_eq_sum_bumps
end
end RHFormalization
