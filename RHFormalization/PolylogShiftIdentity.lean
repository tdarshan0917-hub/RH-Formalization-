import RHFormalization.PolylogStageClosedForm
import RHFormalization.PrimePowerSumConvergence
import Mathlib

/-! PL-4a: Dirichlet shift factorization and the Ioc-to-range index bridge. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

theorem cpow_ofReal_natCast {k : ℕ} (δ : ℝ) :
    ((k : ℂ)) ^ ((δ : ℝ) : ℂ) = (((k : ℝ) ^ δ : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ)) δ
  first
    | exact_mod_cast h.symm
    | (rw [Complex.ofReal_natCast] at h; exact h.symm)

theorem vonMangoldt_term_shift (ρ : ℂ) (δ : ℝ) {k : ℕ} (hk : k ≠ 0) :
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (ρ + ((δ : ℝ) : ℂ)) k
      = LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ k
          * (((k : ℝ) ^ (-δ) : ℝ) : ℂ) := by
  have hk0 : ((k : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [vonMangoldt_term_eq (s := ρ + ((δ : ℝ) : ℂ)) hk, vonMangoldt_term_eq (s := ρ) hk,
    Complex.cpow_add _ _ hk0, cpow_ofReal_natCast δ,
    Real.rpow_neg hkR.le, Complex.ofReal_inv, ← div_eq_mul_inv, div_div]

theorem sum_Ioc_eq_sum_range_succ {α : Type*} [AddCommMonoid α] (f : ℕ → α) (M : ℕ) :
    ∑ k ∈ Finset.Ioc 0 M, f k = ∑ j ∈ Finset.range M, f (j + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hins : Finset.Ioc 0 (M + 1) = insert (M + 1) (Finset.Ioc 0 M) := by
      ext j
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [Finset.sum_range_succ, ← ih, hins, Finset.sum_insert (by simp), add_comm]

theorem partialSum_shift_eq (ρ : ℂ) (δ : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Ioc 0 M,
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (ρ + ((δ : ℝ) : ℂ)) k
      = ∑ j ∈ Finset.range M,
          (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ρ (j + 1))
            * ((((j : ℝ) + 1) ^ (-δ) : ℝ) : ℂ) := by
  rw [sum_Ioc_eq_sum_range_succ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [vonMangoldt_term_shift ρ δ (Nat.succ_ne_zero j)]
  push_cast
  rfl

#print axioms vonMangoldt_term_shift
#print axioms partialSum_shift_eq

end

end RHFormalization
