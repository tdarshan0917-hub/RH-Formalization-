import RHFormalization.DenseTraceCS
import Mathlib

/-!
# DenseEnergyLowerBound — KB1: diagonal lower bound on the perturbed energy

`Q^V_n(a) ≥ (1/2L) Σ_k C_kk² / (λ_k + a + ε_n)` where `ε_n = denseVrate n`.
Proof: `Tr(Cᵀ A⁻¹ C) = Σ_k c_k ⬝ A⁻¹ c_k` (c_k = column k), and for each k
the banked CS `(e_k ⬝ c_k)² ≤ (e_k ⬝ A e_k)(c_k ⬝ A⁻¹ c_k)` with
`e_k ⬝ A e_k = A_kk = λ_k + a + V_kk ≤ λ_k + a + ε_n`.
Pure matrix algebra on banked objects; the first brick of the B8 kill theorem.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators
open Matrix

/-- Trace of `Cᵀ A⁻¹ C` as a sum of column quadratic forms. -/
theorem trace_transpose_inv_mul_eq_sum_cols {N : ℕ}
    (C B : Matrix (Fin N) (Fin N) ℝ) :
    (Cᵀ * B * C).trace
      = ∑ k : Fin N, (fun i => C i k) ⬝ᵥ (B *ᵥ fun j => C j k) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- `e_k ⬝ v = v k`. -/
theorem single_dotProduct_eq {N : ℕ} (k : Fin N) (v : Fin N → ℝ) :
    (Pi.single k (1:ℝ)) ⬝ᵥ v = v k := by
  simp [dotProduct, Pi.single_apply]

/-- `e_k ⬝ A e_k = A k k`. -/
theorem single_quadForm_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (k : Fin N) :
    (Pi.single k (1:ℝ)) ⬝ᵥ (A *ᵥ Pi.single k (1:ℝ)) = A k k := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- **KB1**: diagonal lower bound on the perturbed energy. -/
theorem denseQV_ge_diag_sum (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (1 / (2 * denseL n)) *
      ∑ k : Fin (denseN n),
        (denseCenteredMatrix n k k) ^ 2
          / (galerkinLam (denseL n) (k : ℕ) + a + denseVrate n)
      ≤ denseQV n a := by
  have hL : (0:ℝ) < denseL n := denseL_pos n
  have hpos : (0:ℝ) ≤ 1 / (2 * denseL n) := by positivity
  unfold denseQV
  refine mul_le_mul_of_nonneg_left ?_ hpos
  rw [trace_transpose_inv_mul_eq_sum_cols]
  refine Finset.sum_le_sum (fun k _ => ?_)
  set A := denseAV n a with hAdef
  set C := denseCenteredMatrix n with hCdef
  have hA : A.PosDef := denseAV_posDef n ha
  have hsym : ∀ i j, A i j = A j i := by
    intro i j
    have h := congrFun (congrFun (denseAV_transpose_eq n ha) j) i
    rw [Matrix.transpose_apply] at h
    exact h
  have hq : 0 ≤ (fun i => C i k) ⬝ᵥ (A⁻¹ *ᵥ fun j => C j k) :=
    quadForm_nonneg hA.inv.posSemidef _
  have hcs := quadForm_cauchy_schwarz_inv hA hsym (Pi.single k (1:ℝ)) (fun j => C j k)
  rw [single_dotProduct_eq, single_quadForm_eq] at hcs
  have hAkk : A k k ≤ galerkinLam (denseL n) (k : ℕ) + a + denseVrate n := by
    rw [hAdef, denseAV_apply_diag]
    have := denseV_diag_le_rate n k
    linarith
  have hden : 0 < galerkinLam (denseL n) (k : ℕ) + a + denseVrate n := by
    have h1 := galerkinLam_nonneg (denseL n) (k : ℕ)
    have h2 := denseVrate_nonneg n
    linarith
  rw [div_le_iff₀ hden]
  calc (C k k) ^ 2
      ≤ A k k * ((fun i => C i k) ⬝ᵥ (A⁻¹ *ᵥ fun j => C j k)) := hcs
    _ ≤ (galerkinLam (denseL n) (k : ℕ) + a + denseVrate n)
          * ((fun i => C i k) ⬝ᵥ (A⁻¹ *ᵥ fun j => C j k)) :=
        mul_le_mul_of_nonneg_right hAkk hq
    _ = ((fun i => C i k) ⬝ᵥ (A⁻¹ *ᵥ fun j => C j k))
          * (galerkinLam (denseL n) (k : ℕ) + a + denseVrate n) := by ring

#print axioms trace_transpose_inv_mul_eq_sum_cols
#print axioms denseQV_ge_diag_sum

end

end RHFormalization
