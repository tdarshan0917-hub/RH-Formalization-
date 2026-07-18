-- SENTINEL: spike-transfer-rate-m1-v2
import RHFormalization.Duhamel2IntegrandSqrtBound
import Mathlib

/-! # Core brick 1 — D.SPIKE-TRANSFER rate, M=1, integrand level.
`|duhamel2Integrand| ≤ B²·N²` uniformly for `0 ≤ u ≤ t`: the fixed-cutoff
constant whose time integral is the manuscript's `|E₁| ≤ C(L,R)·t`
(D.BFF.5 at M=1). Hypothesis-free. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- Heat weights never exceed 1 at nonnegative time. -/
theorem heatWeight_le_one (L : ℝ) (t : ℝ) (ht : 0 ≤ t) (m : Fin N) :
    heatWeight (N := N) L t m ≤ 1 := by
  unfold heatWeight
  first
    | (apply Real.exp_le_one_iff.mpr
       have h := sq_nonneg (((m : ℝ) + 1) * Real.pi / L)
       nlinarith)
    | (apply Real.exp_le_one_iff.mpr
       first
         | nlinarith [sq_nonneg (((m : ℝ) + 1) * Real.pi / L)]
         | (unfold galerkinLam
            nlinarith [sq_nonneg (((m : ℝ) + 1) * Real.pi / L)])
         | positivity)

/-- The heat sum is at most the dimension. -/
theorem sum_heatWeight_le_card (L : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ m : Fin N, |heatWeight (N := N) L t m|) ≤ (N : ℝ) := by
  have h1 : ∀ m : Fin N, |heatWeight (N := N) L t m| ≤ 1 := by
    intro m
    have hnn : 0 ≤ heatWeight (N := N) L t m := by
      unfold heatWeight
      exact le_of_lt (Real.exp_pos _)
    rw [abs_of_nonneg hnn]
    exact heatWeight_le_one L t ht m
  calc (∑ m : Fin N, |heatWeight (N := N) L t m|)
      ≤ ∑ _m : Fin N, (1:ℝ) := Finset.sum_le_sum (fun m _ => h1 m)
    _ = (N : ℝ) := by simp

/-- **CORE BRICK 1 (D.BFF.5, M=1, integrand level).** The order-2 Duhamel
integrand is bounded by the fixed-cutoff constant `B²·N²` on the simplex. -/
theorem duhamel2Integrand_abs_le_card_sq
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L : ℝ) (hL : 0 < L) (t u : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) :
    |duhamel2Integrand (N := N) δ qs w L t u|
      ≤ ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2 * ((N : ℝ) * (N : ℝ)) := by
  have htu : (0:ℝ) ≤ t - u := by linarith
  refine le_trans (abs_duhamel2Integrand_le (N := N) δ hδ qs w L hL t u) ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have h1 := sum_heatWeight_le_card (N := N) L (t - u) htu
  have h2 := sum_heatWeight_le_card (N := N) L u hu
  have h1n : (0:ℝ) ≤ ∑ n : Fin N, |heatWeight (N := N) L (t - u) n| := by
    positivity
  have hNn : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  exact mul_le_mul h1 h2 (by positivity) hNn

#print axioms heatWeight_le_one
#print axioms sum_heatWeight_le_card
#print axioms duhamel2Integrand_abs_le_card_sq

end

end RHFormalization
