-- SENTINEL: spike-transfer-c1-gap-v1
import RHFormalization.SpikeTransferC1Profile
import Mathlib

/-! # Core brick 4 — the O(t²) gap (D.BFF.5 M=2 shape).
`|t·Σ V_mm e^{−tλ_m} − t·Σ V_mm| ≤ t²·Σ |V_mm|·λ_m`, via `1−e^{−x} ≤ x`.
Together with bricks 2–3: full trace = free + t·Tr(V) + O(t²) at fixed
cutoff — the finite-stage D.SPIKE-TRANSFER expansion, M = 2. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- `|e^{−x} − 1| ≤ x` for `x ≥ 0`. -/
theorem abs_exp_neg_sub_one_le (x : ℝ) (hx : 0 ≤ x) :
    |Real.exp (-x) - 1| ≤ x := by
  have h1 : Real.exp (-x) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- **CORE BRICK 4 (the c₁ gap).** -/
theorem c1_profile_gap_le_t_sq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : 0 ≤ t) :
    |t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m
          * Real.exp (-(t * galerkinLam L (m : ℕ))))
      - t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m)|
      ≤ t ^ 2 * ∑ m : Fin N,
          |galerkinV (N := N) δ qs w L m m| * galerkinLam L (m : ℕ) := by
  have hlam : ∀ m : Fin N, (0:ℝ) ≤ galerkinLam L (m : ℕ) := by
    intro m
    unfold galerkinLam
    positivity
  have hdiff : t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m
          * Real.exp (-(t * galerkinLam L (m : ℕ))))
      - t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m)
      = t * ∑ m : Fin N, galerkinV (N := N) δ qs w L m m
          * (Real.exp (-(t * galerkinLam L (m : ℕ))) - 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hdiff, abs_mul, abs_of_nonneg ht]
  have hsum : |∑ m : Fin N, galerkinV (N := N) δ qs w L m m
        * (Real.exp (-(t * galerkinLam L (m : ℕ))) - 1)|
      ≤ ∑ m : Fin N, |galerkinV (N := N) δ qs w L m m|
          * (t * galerkinLam L (m : ℕ)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact abs_exp_neg_sub_one_le _ (mul_nonneg ht (hlam m))
  calc t * |∑ m : Fin N, galerkinV (N := N) δ qs w L m m
        * (Real.exp (-(t * galerkinLam L (m : ℕ))) - 1)|
      ≤ t * ∑ m : Fin N, |galerkinV (N := N) δ qs w L m m|
          * (t * galerkinLam L (m : ℕ)) :=
        mul_le_mul_of_nonneg_left hsum ht
    _ = t ^ 2 * ∑ m : Fin N,
          |galerkinV (N := N) δ qs w L m m| * galerkinLam L (m : ℕ) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        ring

#print axioms abs_exp_neg_sub_one_le
#print axioms c1_profile_gap_le_t_sq

end

end RHFormalization
