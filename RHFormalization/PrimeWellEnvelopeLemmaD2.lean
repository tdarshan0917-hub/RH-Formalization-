import RHFormalization.PrimeWellEnvelopeLemmaD

/-!
# Prime-well envelope (DQ1), Lemma D.2: the lattice-Gaussian uniform bound

The shell sum is `e^(u/2)·e^(α/8)` times `∑_k exp(-(k log2 - c)²/(2α))` with
`c = u + α/2`. This file bounds that lattice sum uniformly in `c`.
-/

namespace RHFormalization

open Real Filter Asymptotics

/-- The symmetric lattice-Gaussian tail term `exp(-(j log2)²/(2α))`. -/
noncomputable def gaussTail (α : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-((j : ℝ) * Real.log 2)^2 / (2 * α))

theorem gaussTail_nonneg (α : ℝ) (j : ℕ) : 0 ≤ gaussTail α j := Real.exp_nonneg _

/-- The exponent `-(j log2)²/(2α)` plus `j` tends to `-∞`. -/
theorem gaussTailExp_plus_tendsto_atBot (α : ℝ) (hα : 0 < α) :
    Tendsto (fun j : ℕ => (-((j : ℝ) * Real.log 2)^2 / (2 * α)) + (j : ℝ)) atTop atBot := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfac : (fun j : ℕ => (-((j : ℝ) * Real.log 2)^2 / (2 * α)) + (j : ℝ))
      = (fun j : ℕ => (fun x : ℝ =>
          x * (1 - ((Real.log 2)^2/(2*α)) * x) - 0) (j : ℝ)) := by
    funext j; simp only; field_simp; ring
  rw [hfac]
  exact (neg_quadratic_tendsto_atBot ((Real.log 2)^2/(2*α)) 1 0 (by positivity)).comp
    tendsto_natCast_atTop_atTop

/-- **Summability of the symmetric Gaussian tail.** -/
theorem gaussTail_summable (α : ℝ) (hα : 0 < α) : Summable (gaussTail α) := by
  apply summable_of_isBigO_nat (g := fun j => Real.exp (-(j:ℝ))) summable_exp_neg_nat
  apply Asymptotics.IsBigO.of_bound 1
  have htend := gaussTailExp_plus_tendsto_atBot α hα
  have hev : ∀ᶠ j : ℕ in atTop, (-((j : ℝ) * Real.log 2)^2 / (2 * α)) + (j:ℝ) ≤ 0 :=
    htend.eventually_le_atBot 0
  filter_upwards [hev] with j hj
  unfold gaussTail
  simp only [Real.norm_eq_abs, abs_exp, one_mul]
  apply Real.exp_le_exp.mpr
  linarith [hj]

/-- The wider Gaussian tail term `exp(-(log2)²·d²/(8α))` (α effectively replaced by 4α). -/
noncomputable def gaussTailW (α : ℝ) (d : ℕ) : ℝ :=
  Real.exp (-(Real.log 2)^2 * (d : ℝ)^2 / (8 * α))

theorem gaussTailW_nonneg (α : ℝ) (d : ℕ) : 0 ≤ gaussTailW α d := Real.exp_nonneg _

/-- The wide-tail exponent plus `d` tends to `-∞`. -/
theorem gaussTailWExp_plus_tendsto_atBot (α : ℝ) (hα : 0 < α) :
    Tendsto (fun d : ℕ => (-(Real.log 2)^2 * (d : ℝ)^2 / (8 * α)) + (d : ℝ)) atTop atBot := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfac : (fun d : ℕ => (-(Real.log 2)^2 * (d : ℝ)^2 / (8 * α)) + (d : ℝ))
      = (fun d : ℕ => (fun x : ℝ =>
          x * (1 - ((Real.log 2)^2/(8*α)) * x) - 0) (d : ℝ)) := by
    funext d; simp only; field_simp; ring
  rw [hfac]
  exact (neg_quadratic_tendsto_atBot ((Real.log 2)^2/(8*α)) 1 0 (by positivity)).comp
    tendsto_natCast_atTop_atTop

/-- **Summability of the wide Gaussian tail.** -/
theorem gaussTailW_summable (α : ℝ) (hα : 0 < α) : Summable (gaussTailW α) := by
  apply summable_of_isBigO_nat (g := fun d => Real.exp (-(d:ℝ))) summable_exp_neg_nat
  apply Asymptotics.IsBigO.of_bound 1
  have htend := gaussTailWExp_plus_tendsto_atBot α hα
  have hev : ∀ᶠ d : ℕ in atTop, (-(Real.log 2)^2 * (d : ℝ)^2 / (8 * α)) + (d:ℝ) ≤ 0 :=
    htend.eventually_le_atBot 0
  filter_upwards [hev] with d hd
  unfold gaussTailW
  simp only [Real.norm_eq_abs, abs_exp, one_mul]
  apply Real.exp_le_exp.mpr
  linarith [hd]

#print axioms gaussTail_summable
#print axioms gaussTailW_summable

end RHFormalization
