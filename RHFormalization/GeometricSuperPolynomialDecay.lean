import Mathlib
import RHFormalization.DSuperSmoothing

/-!
# Geometric decay ⇒ super-polynomial decay

Plank 2 of the Appendix-D mixed-word connection. The manuscript's Lemma B.TC bounds
the order-`k` Duhamel/mixed-word term geometrically: `|term_k| ≤ (C·t^{3/4})^k`, ratio
`ρ < 1` for small `t`. Any geometrically-decaying sequence satisfies `SuperPolynomialDecay`
— the certificate the finite-stage operator structure needs in `h_mixedWordSuperPolynomialDecay`.

Reuses the single-term exp lower bound `exp x ≥ x^N/N!`: `ρ = exp(-a)`, `a = -log ρ > 0`,
so `ρ^k = exp(-a k) ≤ C_N/(k+1)^N` with explicit `C_N = A·exp(a)·N!/a^N`.
-/

namespace RHFormalization
open Real
noncomputable section

/-- A pure exponential decay `exp(-a·k)` is bounded by `(exp a · N!/a^N)/(k+1)^N`. -/
theorem exp_neg_mul_nat_le_pow
    (a : ℝ) (ha : 0 < a) (N : ℕ) (k : ℕ) :
    Real.exp (-(a * k)) ≤ (Real.exp a * (Nat.factorial N : ℝ) / a ^ N) / ((k + 1 : ℕ) : ℝ) ^ N := by
  have hfact_pos : 0 < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  set y : ℝ := a * (k + 1) with hy
  have hy_pos : 0 < y := by rw [hy]; positivity
  have hyN_pos : 0 < y ^ N := pow_pos hy_pos N
  have hlow : y ^ N / (Nat.factorial N : ℝ) ≤ Real.exp y :=
    Real.pow_div_factorial_le_exp y hy_pos.le N
  have hquot_pos : 0 < y ^ N / (Nat.factorial N : ℝ) := div_pos hyN_pos hfact_pos
  have hbound : Real.exp (-y) ≤ (Nat.factorial N : ℝ) / y ^ N := by
    have hone : 1 / Real.exp y ≤ 1 / (y ^ N / (Nat.factorial N : ℝ)) :=
      one_div_le_one_div_of_le hquot_pos hlow
    rw [Real.exp_neg, ← one_div]
    rw [one_div_div] at hone
    exact hone
  have hsplit : Real.exp (-(a * k)) = Real.exp a * Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    rw [hy]; push_cast; ring
  rw [hsplit]
  have hexp_a_pos : 0 < Real.exp a := Real.exp_pos a
  calc Real.exp a * Real.exp (-y)
      ≤ Real.exp a * ((Nat.factorial N : ℝ) / y ^ N) := by
        apply mul_le_mul_of_nonneg_left hbound hexp_a_pos.le
    _ = (Real.exp a * (Nat.factorial N : ℝ) / a ^ N) / ((k + 1 : ℕ) : ℝ) ^ N := by
        rw [hy, mul_pow]
        field_simp
        push_cast
        ring

/-- **Geometric ⇒ super-polynomial decay (Plank 2).** -/
theorem superPolynomialDecay_of_geometric
    (A ρ : ℝ) (hA : 0 ≤ A) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (r : ℕ → ℝ) (hr : ∀ k, r k ≤ A * ρ ^ k) :
    SuperPolynomialDecay r := by
  intro N
  set a : ℝ := -Real.log ρ with hadef
  have ha_pos : 0 < a := by
    rw [hadef, neg_pos]; exact Real.log_neg hρ0 hρ1
  refine ⟨A * (Real.exp a * (Nat.factorial N : ℝ) / a ^ N), by positivity, ?_⟩
  intro k
  have hρexp : ρ ^ k = Real.exp (-(a * k)) := by
    have hkey : Real.exp (-(a * k)) = ρ ^ k := by
      rw [hadef]
      rw [show -(-Real.log ρ * (k : ℝ)) = (k : ℝ) * Real.log ρ by ring]
      rw [Real.exp_nat_mul, Real.exp_log hρ0]
    exact hkey.symm
  calc r k ≤ A * ρ ^ k := hr k
    _ = A * Real.exp (-(a * k)) := by rw [hρexp]
    _ ≤ A * ((Real.exp a * (Nat.factorial N : ℝ) / a ^ N) / ((k + 1 : ℕ) : ℝ) ^ N) := by
        apply mul_le_mul_of_nonneg_left (exp_neg_mul_nat_le_pow a ha_pos N k) hA
    _ = (A * (Real.exp a * (Nat.factorial N : ℝ) / a ^ N)) / ((k + 1 : ℕ) : ℝ) ^ N := by
        ring

#print axioms superPolynomialDecay_of_geometric
end
end RHFormalization
