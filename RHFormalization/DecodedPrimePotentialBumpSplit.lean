import RHFormalization.PrimePotentialDecodedCenter

/-!
# Brick 2, stone 2: single-bump decomposition `V_{mn} = ∑_q w(q)·B_{mn}(q)`.
-/

set_option autoImplicit false

-- SENTINEL: decoded-prime-potential-bump-split-v2

namespace RHFormalization
noncomputable section
open Real MeasureTheory intervalIntegral
open scoped Real

/-- Single-bump matrix element. -/
noncomputable def decodedBumpMatrixElement
    (δ : ℝ) (q : ℕ) (L : ℝ) (m n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..L,
    dirichletEigenfun m L x * gaussBump δ (x - (ppDecode q).center) * dirichletEigenfun n L x

theorem decoded_continuous_summand (δ : ℝ) (q : ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) :
    Continuous (fun x : ℝ =>
      w q * (dirichletEigenfun m L x * gaussBump δ (x - (ppDecode q).center) * dirichletEigenfun n L x)) := by
  unfold dirichletEigenfun gaussBump
  fun_prop

theorem decoded_integrand_sum_eq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) (x : ℝ) :
    dirichletEigenfun m L x * (∑ q ∈ qs, w q * gaussBump δ (x - (ppDecode q).center))
        * dirichletEigenfun n L x
      = ∑ q ∈ qs,
          w q * (dirichletEigenfun m L x * gaussBump δ (x - (ppDecode q).center)
                  * dirichletEigenfun n L x) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem decodedVmatrixElement_eq_sum_bumps
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) :
    decodedVmatrixElement δ qs w L m n
      = ∑ q ∈ qs, w q * decodedBumpMatrixElement δ q L m n := by
  unfold decodedVmatrixElement decodedPrimePotentialFn
  rw [intervalIntegral.integral_congr
        (g := fun x =>
          ∑ q ∈ qs, w q * (dirichletEigenfun m L x * gaussBump δ (x - (ppDecode q).center)
                            * dirichletEigenfun n L x))
        (fun x _ => decoded_integrand_sum_eq δ qs w L m n x)]
  rw [intervalIntegral.integral_finsetSum
        (fun q _ => (decoded_continuous_summand δ q w L m n).intervalIntegrable 0 L)]
  apply Finset.sum_congr rfl
  intro q _
  unfold decodedBumpMatrixElement
  rw [intervalIntegral.integral_const_mul]

#print axioms decodedVmatrixElement_eq_sum_bumps
end
end RHFormalization
