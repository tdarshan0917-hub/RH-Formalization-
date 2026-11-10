import RHFormalization.PrimeGraphRealLevels
import Mathlib

/-!
# PrimeGraphJacobi — PG-6: Jacobi's formula and the secular determinant's derivative

* `hasDerivAt_det_adjugate`: for an entrywise-differentiable matrix path `A(k)`,
  `d/dk det A(k) = Tr(adj A · A')` (Leibniz expansion → column regrouping → Cramer).
* `hasDerivAt_det_of_isUnit`: at an invertible point, `d/dk det A = det A · Tr(A⁻¹ A')`.
* `secularDet_hasDerivAt`: for `U(k) = diag(p^{ik})·σ`, `d/dk (1 - U) = -(i Λ U)` with
  `Λ = diag(log p)`, hence `d/dk det(1-U) = det(1-U) · Tr((1-U)⁻¹ · (-(i Λ U)))`.
  Equivalently `i · (log det(1-U))' = Tr(Λ U (1-U)⁻¹)`: the trace-formula density is the
  log-derivative of the secular determinant, whose zeros are the (real, PG-5) levels.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix
open scoped BigOperators

section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem hasDerivAt_det_leibniz (A : ℂ → Matrix n n ℂ) (A' : Matrix n n ℂ) (x : ℂ)
    (hA : ∀ i j, HasDerivAt (fun k => A k i j) (A' i j) x) :
    HasDerivAt (fun k => (A k).det)
      (∑ τ : Equiv.Perm n, ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, A x (τ j) j) * A' (τ i) i) x := by
  have hfun : (fun k => (A k).det)
      = fun k => ∑ τ : Equiv.Perm n, ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ i, A k (τ i) i := by
    funext k
    exact Matrix.det_apply' _
  rw [hfun]
  refine HasDerivAt.fun_sum (fun τ _ => ?_)
  refine HasDerivAt.const_mul _ ?_
  first
    | exact HasDerivAt.fun_finsetProd (fun i _ => hA (τ i) i)
    | exact HasDerivAt.fun_finset_prod (fun i _ => hA (τ i) i)
    | simpa [smul_eq_mul] using HasDerivAt.fun_finsetProd (fun i _ => hA (τ i) i)

theorem det_updateCol_expand (M : Matrix n n ℂ) (i : n) (b : n → ℂ) :
    (M.updateCol i b).det = ∑ τ : Equiv.Perm n, ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      ((∏ j ∈ Finset.univ.erase i, M (τ j) j) * b (τ i)) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  congr 1
  have h := Finset.mul_prod_erase Finset.univ (fun j => M.updateCol i b (τ j) j)
    (Finset.mem_univ i)
  try beta_reduce at h
  rw [← h, Matrix.updateCol_self, mul_comm (b (τ i))]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Matrix.updateCol_apply, if_neg (Finset.ne_of_mem_erase hj)]

theorem sum_det_updateCol_eq_trace (M B : Matrix n n ℂ) :
    ∑ i, (M.updateCol i (fun r => B r i)).det = (M.adjugate * B).trace := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  first
    | rfl
    | simp only [Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    | simp [Matrix.mulVec, Matrix.mul_apply]

/-- **Jacobi's formula (adjugate form).** -/
theorem hasDerivAt_det_adjugate (A : ℂ → Matrix n n ℂ) (A' : Matrix n n ℂ) (x : ℂ)
    (hA : ∀ i j, HasDerivAt (fun k => A k i j) (A' i j) x) :
    HasDerivAt (fun k => (A k).det) ((A x).adjugate * A').trace x := by
  have h1 := hasDerivAt_det_leibniz A A' x hA
  convert h1 using 1
  rw [← sum_det_updateCol_eq_trace]
  simp only [det_updateCol_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.mul_sum]
  all_goals (refine Finset.sum_congr rfl (fun i _ => ?_); rfl)

/-- **Jacobi's formula at an invertible point.** -/
theorem hasDerivAt_det_of_isUnit (A : ℂ → Matrix n n ℂ) (A' : Matrix n n ℂ) (x : ℂ)
    (hA : ∀ i j, HasDerivAt (fun k => A k i j) (A' i j) x) (hdet : IsUnit (A x).det) :
    HasDerivAt (fun k => (A k).det) ((A x).det * ((A x)⁻¹ * A').trace) x := by
  have hadj : (A x).adjugate = (A x).det • (A x)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hdet, one_smul]
  have h := hasDerivAt_det_adjugate A A' x hA
  rw [hadj] at h
  first
    | (rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h; exact h)
    | (rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul] at h; exact h)
    | simpa [Matrix.smul_mul, Matrix.trace_smul] using h

end Jacobi

/-- The prime-graph quantum map `U(k) = diag(p^{ik})·σ`. -/
noncomputable def graphU {ι : Type*} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    (σ : Matrix ι ι ℂ) (k : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun b => ((pr b : ℕ) : ℂ) ^ (Complex.I * k)) * σ

theorem graphU_entry_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ) (x : ℂ) (i j : ι) :
    HasDerivAt (fun k => (1 - graphU pr σ k) i j)
      ((-(Complex.I • (Matrix.diagonal (fun b => Complex.log ((pr b : ℕ) : ℂ)) *
        graphU pr σ x))) i j) x := by
  have hp0 : ((pr i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hpr i).ne_zero
  have hfe : (fun k => (1 - graphU pr σ k) i j)
      = fun k => (1 : Matrix ι ι ℂ) i j - ((pr i : ℕ) : ℂ) ^ (Complex.I * k) * σ i j := by
    funext k
    rw [Matrix.sub_apply, graphU, Matrix.diagonal_mul]
  rw [hfe]
  have hcp : HasDerivAt (fun k => ((pr i : ℕ) : ℂ) ^ (Complex.I * k))
      (((pr i : ℕ) : ℂ) ^ (Complex.I * x) * Complex.log ((pr i : ℕ) : ℂ) * (Complex.I * 1)) x :=
    ((hasDerivAt_id' x).const_mul Complex.I).const_cpow (Or.inl hp0)
  refine ((hasDerivAt_const x ((1 : Matrix ι ι ℂ) i j)).sub
    (hcp.mul_const (σ i j))).congr_deriv ?_
  rw [graphU]
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul]
  ring

/-- **PG-6 — derivative of the secular determinant.** -/
theorem secularDet_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ) (x : ℂ)
    (hdet : IsUnit (1 - graphU pr σ x).det) :
    HasDerivAt (fun k => (1 - graphU pr σ k).det)
      ((1 - graphU pr σ x).det *
        ((1 - graphU pr σ x)⁻¹ * -(Complex.I • (Matrix.diagonal
          (fun b => Complex.log ((pr b : ℕ) : ℂ)) * graphU pr σ x))).trace) x :=
  hasDerivAt_det_of_isUnit (fun k => 1 - graphU pr σ k) _ x
    (fun i j => graphU_entry_hasDerivAt pr hpr σ x i j) hdet

/-- PG-6 off the real axis (upper half-plane), no invertibility hypothesis. -/
theorem secularDet_hasDerivAt_upper {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ)
    (hσ : σ ∈ unitary (Matrix ι ι ℂ)) (x : ℂ) (hx : 0 < x.im) :
    HasDerivAt (fun k => (1 - graphU pr σ k).det)
      ((1 - graphU pr σ x).det *
        ((1 - graphU pr σ x)⁻¹ * -(Complex.I • (Matrix.diagonal
          (fun b => Complex.log ((pr b : ℕ) : ℂ)) * graphU pr σ x))).trace) x :=
  secularDet_hasDerivAt pr hpr σ x
    (graphMap_one_sub_isUnit_det _ σ hσ (fun b => primePhase_norm_lt_one (hpr b) hx))

#print axioms hasDerivAt_det_adjugate
#print axioms hasDerivAt_det_of_isUnit
#print axioms secularDet_hasDerivAt
#print axioms secularDet_hasDerivAt_upper

end RHFormalization
