import RHFormalization.PrimeWellEnvelopeLemmaC
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Prime-well envelope (DQ1), Lemma D: the geometric-Gaussian shell series

Step 1: summability. Step 2 keystone: completing the square, which exhibits the
shell sum as `e^(u/2)·e^(α/8)` times a lattice-sampled Gaussian.
-/

namespace RHFormalization

open Real Filter Asymptotics

/-- The geometric-Gaussian shell term. -/
noncomputable def shellTerm (α u : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt 2 ^ k * Real.exp (-((k : ℝ) * Real.log 2 - u)^2 / (2 * α))

theorem shellTerm_nonneg (α u : ℝ) (k : ℕ) : 0 ≤ shellTerm α u k :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_nonneg _)

/-- `√2 = exp(log 2 / 2)`. -/
theorem sqrt_two_eq_exp : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  ring_nf

/-- The shell term as a single exponential. -/
theorem shellTerm_eq_exp (α u : ℝ) (k : ℕ) :
    shellTerm α u k
      = Real.exp ((k : ℝ) * (Real.log 2 / 2) - ((k : ℝ) * Real.log 2 - u)^2 / (2 * α)) := by
  unfold shellTerm
  rw [sqrt_two_eq_exp, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- A negative-leading quadratic `x·(b - A·x) - c` tends to `-∞` for `A > 0`. -/
theorem neg_quadratic_tendsto_atBot (A b c : ℝ) (hA : 0 < A) :
    Tendsto (fun x : ℝ => x * (b - A * x) - c) atTop atBot := by
  apply Filter.tendsto_atBot_add_const_right
  apply Filter.Tendsto.atTop_mul_atBot₀ tendsto_id
  apply Filter.tendsto_atBot_add_const_left
  have h : Tendsto (fun x : ℝ => x * (-A)) atTop atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg' (neg_neg_of_pos hA) tendsto_id
  simpa [mul_comm, neg_mul, mul_neg] using h

/-- The shell exponent plus `k`, written as a quadratic, tends to `-∞`. -/
theorem shellExponent_plus_tendsto_atBot (α u : ℝ) (hα : 0 < α) :
    Tendsto (fun k : ℕ =>
      ((k : ℝ) * (Real.log 2 / 2) - ((k : ℝ) * Real.log 2 - u)^2 / (2 * α)) + (k : ℝ))
      atTop atBot := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfac : (fun k : ℕ =>
      ((k : ℝ) * (Real.log 2 / 2) - ((k : ℝ) * Real.log 2 - u)^2 / (2 * α)) + (k : ℝ))
      = (fun k : ℕ => (fun x : ℝ =>
          x * ((Real.log 2/2 + u*Real.log 2/α + 1) - ((Real.log 2)^2/(2*α)) * x)
          - u^2/(2*α)) (k : ℝ)) := by
    funext k; simp only; field_simp; ring
  rw [hfac]
  exact (neg_quadratic_tendsto_atBot ((Real.log 2)^2/(2*α))
    (Real.log 2/2 + u*Real.log 2/α + 1) (u^2/(2*α)) (by positivity)).comp
    tendsto_natCast_atTop_atTop

/-- **Lemma D.1 (summability).** The geometric-Gaussian shell series is summable. -/
theorem shellTerm_summable (α u : ℝ) (hα : 0 < α) : Summable (shellTerm α u) := by
  apply summable_of_isBigO_nat (g := fun k => Real.exp (-(k:ℝ))) summable_exp_neg_nat
  apply Asymptotics.IsBigO.of_bound 1
  have htend := shellExponent_plus_tendsto_atBot α u hα
  have hev : ∀ᶠ k : ℕ in atTop,
      ((k : ℝ) * (Real.log 2 / 2) - ((k : ℝ) * Real.log 2 - u)^2 / (2 * α)) + (k:ℝ) ≤ 0 :=
    htend.eventually_le_atBot 0
  filter_upwards [hev] with k hk
  rw [shellTerm_eq_exp α u k]
  simp only [Real.norm_eq_abs, abs_exp, one_mul]
  apply Real.exp_le_exp.mpr
  linarith [hk]

/-- **Completing the square.** The shell term factors as
`e^(u/2) · e^(α/8) · exp(-(k log2 - u - α/2)²/(2α))` — a Gaussian in the lattice
point `k log2`, centered at `u + α/2`, times the `e^(u/2)` envelope factor. -/
theorem shellTerm_completeSquare (α u : ℝ) (k : ℕ) (hα : 0 < α) :
    shellTerm α u k
      = Real.exp (u/2) * Real.exp (α/8)
        * Real.exp (-((k : ℝ) * Real.log 2 - u - α/2)^2 / (2 * α)) := by
  rw [shellTerm_eq_exp α u k, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

#print axioms shellTerm_summable
#print axioms shellTerm_completeSquare

end RHFormalization
