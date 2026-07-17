import Mathlib
import RHFormalization.EnvDomEnvelopePos
import RHFormalization.EnvDomEnvelopeNeg
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Real

namespace RHFormalization

/-- The confining envelope `V_env(u) = A(1 + u² + e^u)` (manuscript p.53). -/
noncomputable def Venv (A u : ℝ) : ℝ := A * (1 + u ^ 2 + Real.exp u)

/-- **A-FINAL (A.ENV-DOM packaged shape).** The abstract shell tsum is bounded by
`K·(1 + u² + e^u)` for ALL `u`, combining the banked `u≤0` half
(`envelope_neg_final`) and `u>0` half (`envelope_pos_final`) by cases. `K` is the
max of the two half-constants. This is the all-ℝ pointwise envelope that
A.ENV-FORM (KLMN form bound, Phase B) consumes. Uses the FROZEN √q normalization
(the shell coefficient's e^{k/2} is population×per-term, memory/handoff frozen). -/
theorem shell_tsum_envelope_all
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) :
    ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ (Real.exp (1 / (16 * κ')) * 73
          + ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
              * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2)
          + ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
              * Real.exp (-κ' * (k : ℝ) ^ 2))
        * (1 + u ^ 2 + Real.exp u) := by
  -- nonneg envelope multiplier
  have henvpos : (0:ℝ) ≤ 1 + u ^ 2 + Real.exp u := by
    have := Real.exp_pos u; nlinarith [sq_nonneg u]
  -- the two half-constants, both nonneg
  set Cpos : ℝ := Real.exp (1 / (16 * κ')) * 73
      + ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) with hCpos
  set Cneg : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
      * Real.exp (-κ' * (k : ℝ) ^ 2) with hCneg
  have hCpos_nn : 0 ≤ Cpos := by
    rw [hCpos]
    have h1 : (0:ℝ) ≤ Real.exp (1 / (16 * κ')) * 73 := by positivity
    have h2 : (0:ℝ) ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) := by
      apply tsum_nonneg; intro k; positivity
    linarith
  have hCneg_nn : 0 ≤ Cneg := by
    rw [hCneg]; apply tsum_nonneg; intro k; positivity
  rcases le_or_gt u 0 with hu | hu
  · -- u ≤ 0 : use envelope_neg_final, bound Cneg·env ≤ (Cpos+Cneg)·env
    have hneg := envelope_neg_final κ' hκ' u hu
    calc ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
            * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        ≤ Cneg * (1 + u ^ 2 + Real.exp u) := by rw [hCneg]; exact hneg
      _ ≤ (Cpos + Cneg) * (1 + u ^ 2 + Real.exp u) := by
          apply mul_le_mul_of_nonneg_right _ henvpos
          linarith [hCpos_nn]
  · -- u > 0 : use envelope_pos_final, bound Cpos·env ≤ (Cpos+Cneg)·env
    have hpos := envelope_pos_final κ' hκ' u hu
    calc ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
            * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        ≤ Cpos * (1 + u ^ 2 + Real.exp u) := by rw [hCpos]; exact hpos
      _ ≤ (Cpos + Cneg) * (1 + u ^ 2 + Real.exp u) := by
          apply mul_le_mul_of_nonneg_right _ henvpos
          linarith [hCneg_nn]

#print axioms shell_tsum_envelope_all

end RHFormalization
