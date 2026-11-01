import RHFormalization.PrimeGraphContraction
import Mathlib

/-!
# PrimeGraphRealLevels — PG-5: every level of the prime quantum graph is real

Secular determinant `det(1 - U(k))`, `U(k) = diag(p^{ik})·σ`, `σ` unitary.
* `Im k > 0`: `‖U‖ < 1` (PG-4), so `1 - U` is invertible.
* `Im k < 0`: `1 - U = -(U·(1 - σ*·diag(p^{-ik})))` and `‖σ*·diag(p^{-ik})‖ ≤ max p^{Im k} < 1`.
Hence `det(1 - U(k)) = 0 → Im k = 0`: the graph's exact analogue of RH, forced by unitarity.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem unitary_mul_star_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ ∈ unitary (Matrix n n ℂ)) : σ * star σ = 1 := by
  first
    | exact unitary.mul_star_self_of_mem hσ
    | exact Unitary.mul_star_self_of_mem hσ
    | exact (unitary.mem_iff.mp hσ).2

theorem unitary_star_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ ∈ unitary (Matrix n n ℂ)) : star σ * σ = 1 := by
  first
    | exact unitary.star_mul_self_of_mem hσ
    | exact Unitary.star_mul_self_of_mem hσ
    | exact (unitary.mem_iff.mp hσ).1

theorem unitary_star_mem' {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ ∈ unitary (Matrix n n ℂ)) : star σ ∈ unitary (Matrix n n ℂ) := by
  first
    | exact unitary.star_mem hσ
    | exact Unitary.star_mem hσ
    | exact unitary.mem_iff.mpr
        ⟨by rw [star_star]; exact unitary_mul_star_eq_one hσ,
         by rw [star_star]; exact unitary_star_mul_eq_one hσ⟩

/-- Lower half-plane: if `z·w = 1` entrywise and `‖w‖ < 1`, then `1 - diag(z)·σ` is invertible. -/
theorem graphMap_lower_isUnit_det {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (z w : n → ℂ) (σ : Matrix n n ℂ) (hσ : σ ∈ unitary (Matrix n n ℂ))
    (hzw : ∀ b, z b * w b = 1) (hw : ∀ b, ‖w b‖ < 1) :
    IsUnit (1 - Matrix.diagonal z * σ).det := by
  have hV : ‖star σ * Matrix.diagonal w‖ < 1 := by
    have h1 : ‖star σ‖ = 1 := CStarRing.norm_of_mem_unitary (unitary_star_mem' hσ)
    have hmul : ‖star σ * Matrix.diagonal w‖ ≤ ‖star σ‖ * ‖Matrix.diagonal w‖ :=
      Matrix.l2_opNorm_mul _ _
    have hd : ‖Matrix.diagonal w‖ = ‖w‖ := Matrix.l2_opNorm_diagonal w
    have hw' : ‖w‖ < 1 := (pi_norm_lt_iff one_pos).2 hw
    rw [hd] at hmul
    first
      | (rw [h1, one_mul] at hmul; exact lt_of_le_of_lt hmul hw')
      | (simp only [h1, one_mul] at hmul; exact lt_of_le_of_lt hmul hw')
      | nlinarith [hmul, hw', h1, norm_nonneg w]
  have hkey : Matrix.diagonal z * σ * (star σ * Matrix.diagonal w) = 1 := by
    rw [mul_assoc, ← mul_assoc σ, unitary_mul_star_eq_one hσ, one_mul,
      Matrix.diagonal_mul_diagonal]
    have hf : (fun b => z b * w b) = fun _ => (1 : ℂ) := funext hzw
    rw [hf]
    exact Matrix.diagonal_one
  have hfac : 1 - Matrix.diagonal z * σ
      = -(Matrix.diagonal z * σ * (1 - star σ * Matrix.diagonal w)) := by
    rw [mul_sub, mul_one, hkey, neg_sub]
  rw [hfac, Matrix.det_neg, Matrix.det_mul, Matrix.det_mul, isUnit_iff_ne_zero]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun b _ => left_ne_zero_of_mul_eq_one (hzw b))
  · exact (Matrix.isUnit_det_of_left_inverse (unitary_star_mul_eq_one hσ)).ne_zero
  · exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.oneSub _ hV).isUnit).ne_zero

/-- **PG-5 — all levels of the prime graph are real.** If the secular determinant
`det(1 - diag(p^{ik})·σ)` vanishes, with `σ` unitary, then `Im k = 0`. -/
theorem primeGraph_levels_real {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ)
    (hσ : σ ∈ unitary (Matrix ι ι ℂ)) (k : ℂ)
    (hdet : (1 - Matrix.diagonal (fun b => ((pr b : ℕ) : ℂ) ^ (Complex.I * k)) * σ).det = 0) :
    k.im = 0 := by
  rcases lt_trichotomy k.im 0 with h | h | h
  · exfalso
    have hzw : ∀ b, ((pr b : ℕ) : ℂ) ^ (Complex.I * k) * ((pr b : ℕ) : ℂ) ^ (Complex.I * -k) = 1 := by
      intro b
      have hp0 : ((pr b : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hpr b).ne_zero
      rw [← Complex.cpow_add _ _ hp0]
      first
        | rw [mul_neg, add_neg_cancel, Complex.cpow_zero]
        | simp
    have hw : ∀ b, ‖((pr b : ℕ) : ℂ) ^ (Complex.I * -k)‖ < 1 :=
      fun b => primePhase_norm_lt_one (hpr b) (by rw [Complex.neg_im]; linarith)
    have hu := graphMap_lower_isUnit_det _ _ σ hσ hzw hw
    rw [hdet] at hu
    exact not_isUnit_zero hu
  · exact h
  · exfalso
    have hz : ∀ b, ‖((pr b : ℕ) : ℂ) ^ (Complex.I * k)‖ < 1 :=
      fun b => primePhase_norm_lt_one (hpr b) h
    have hu := graphMap_one_sub_isUnit_det _ σ hσ hz
    rw [hdet] at hu
    exact not_isUnit_zero hu

#print axioms graphMap_lower_isUnit_det
#print axioms primeGraph_levels_real

end RHFormalization
