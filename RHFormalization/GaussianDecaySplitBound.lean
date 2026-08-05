import RHFormalization.BumpMatrixElementErrorBound
import Mathlib

/-!
# GaussianDecaySplitBound — the per-prime error majorant, schedule-ready

ROUTE CARD
1. Target: for `2 ≤ q`, `log q ≤ R`, `R + 1 ≤ L`:
   `gaussianDecayBound 1 q L
      ≤ gaussSplitC·e^{−½(log q)²} + gaussSplitC·(e^{−½(L−R)²}/(L−R))`,
   `gaussSplitC = 2/(√(2π)·log 2)`. Term 1 is schedule-independent and
   summable against `Λ(q)/√q` (Gaussian-in-center, banked GaussianCore
   donor); term 2 is q-independent and crushed by the schedule gap
   `admL − admR`.
2. Raw B on Ω? NO. B−M bare Prop? NO — real inequalities only.
3. Consumer: error summation (audit task 3):
   `Σ_{q∈active(admR n)} |w q|·gaussianDecayBound 1 q (admL n) ≤ C`
   uniformly in n → errPart is eps-class in the provider.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real

/-- The common majorant constant. -/
noncomputable def gaussSplitC : ℝ := 2 / (Real.sqrt (2 * Real.pi) * Real.log 2)

theorem gaussSplitC_pos : 0 < gaussSplitC := by
  unfold gaussSplitC
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (0:ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.mpr
    positivity
  positivity

/-- `2/√(2π) ≤ gaussSplitC` (since `log 2 ≤ 1`). -/
theorem two_div_sqrt_le_gaussSplitC :
    2 / Real.sqrt (2 * Real.pi) ≤ gaussSplitC := by
  unfold gaussSplitC
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num)
    linarith
  have hs : (0:ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.mpr
    positivity
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  calc Real.sqrt (2 * Real.pi) * Real.log 2
      ≤ Real.sqrt (2 * Real.pi) * 1 := by
        exact mul_le_mul_of_nonneg_left hlog2_le1 hs.le
    _ = Real.sqrt (2 * Real.pi) := mul_one _

/-- **The split majorant** for the banked B10 decay bound at δ = 1. -/
theorem gaussianDecayBound_le_split (q : ℕ) (R L : ℝ)
    (hq2 : 2 ≤ q) (hqR : Real.log q ≤ R) (hRL : R + 1 ≤ L) :
    gaussianDecayBound 1 q L
      ≤ gaussSplitC * Real.exp (-(1/2 * (Real.log q)^2))
        + gaussSplitC * (Real.exp (-(1/2 * (L - R)^2)) / (L - R)) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hq2' : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
  have hlogq : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) hq2'
  have hlogq_pos : (0:ℝ) < Real.log q := lt_of_lt_of_le hlog2 hlogq
  have hLR_pos : (0:ℝ) < L - R := by linarith
  have hLq : L - R ≤ L - Real.log q := by linarith
  have hLq_pos : (0:ℝ) < L - Real.log q := lt_of_lt_of_le hLR_pos hLq
  have hs : (0:ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.mpr
    positivity
  unfold gaussianDecayBound
  simp only [one_pow, mul_one]
  -- both prefactors now 1/√(2π), both rates 1/2
  have hT1 : (1 / Real.sqrt (2*Real.pi))
        * (Real.exp (-(1/2 * (Real.log q)^2)) / ((1/2) * Real.log q))
      ≤ gaussSplitC * Real.exp (-(1/2 * (Real.log q)^2)) := by
    have hstep : (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (Real.log q)^2)) / ((1/2) * Real.log q))
        ≤ (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (Real.log q)^2)) / ((1/2) * Real.log 2)) := by
      gcongr
    have hclose : (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (Real.log q)^2)) / ((1/2) * Real.log 2))
        = gaussSplitC * Real.exp (-(1/2 * (Real.log q)^2)) := by
      unfold gaussSplitC
      field_simp
    calc (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (Real.log q)^2)) / ((1/2) * Real.log q))
        ≤ (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (Real.log q)^2)) / ((1/2) * Real.log 2)) := hstep
      _ = gaussSplitC * Real.exp (-(1/2 * (Real.log q)^2)) := hclose
  have hT2 : (1 / Real.sqrt (2*Real.pi))
        * (Real.exp (-(1/2 * (L - Real.log q)^2)) / ((1/2) * (L - Real.log q)))
      ≤ gaussSplitC * (Real.exp (-(1/2 * (L - R)^2)) / (L - R)) := by
    have hE2 : Real.exp (-(1/2 * (L - Real.log q)^2))
        ≤ Real.exp (-(1/2 * (L - R)^2)) := by
      apply Real.exp_le_exp.mpr
      have hsq : (L - R)^2 ≤ (L - Real.log q)^2 := by
        apply sq_le_sq'
        · linarith
        · exact hLq
      linarith
    have hstep : (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (L - Real.log q)^2)) / ((1/2) * (L - Real.log q)))
        ≤ (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (L - R)^2)) / ((1/2) * (L - R))) := by
      gcongr <;> linarith
    have hEq : (1 / Real.sqrt (2*Real.pi))
        * (Real.exp (-(1/2 * (L - R)^2)) / ((1/2) * (L - R)))
        = (2 / Real.sqrt (2*Real.pi))
            * (Real.exp (-(1/2 * (L - R)^2)) / (L - R)) := by
      field_simp
    have hER : (0:ℝ) ≤ Real.exp (-(1/2 * (L - R)^2)) / (L - R) := by
      positivity
    calc (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (L - Real.log q)^2)) / ((1/2) * (L - Real.log q)))
        ≤ (1 / Real.sqrt (2*Real.pi))
          * (Real.exp (-(1/2 * (L - R)^2)) / ((1/2) * (L - R))) := hstep
      _ = (2 / Real.sqrt (2*Real.pi))
            * (Real.exp (-(1/2 * (L - R)^2)) / (L - R)) := hEq
      _ ≤ gaussSplitC * (Real.exp (-(1/2 * (L - R)^2)) / (L - R)) :=
          mul_le_mul_of_nonneg_right two_div_sqrt_le_gaussSplitC hER
  exact add_le_add hT1 hT2

#print axioms gaussSplitC_pos
#print axioms two_div_sqrt_le_gaussSplitC
#print axioms gaussianDecayBound_le_split

end

end RHFormalization
