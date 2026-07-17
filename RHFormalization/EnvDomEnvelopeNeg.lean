import Mathlib
import RHFormalization.EnvDomShellNegSum
import RHFormalization.EnvDomShellPosTail
import RHFormalization.EnvDomShellGaussian
import RHFormalization.EnvDomShellSumBound
set_option autoImplicit false
open Real Finset

namespace RHFormalization

/-- **A.ENV-DOM envelope, u≤0 closed form.** For `u ≤ 0` and `0 < κ'`, the shell
tsum is bounded by an absolute constant `Kbound κ' := ∑' shell coefficient`.
This packages the banked `shell_neg_tsum_le` into the envelope shape: for `u≤0`,
`V_∞^#`-type shell sums are `≤ C ≤ C(1+u²+e^u)` (since `1+u²+e^u ≥ 1`). -/
theorem envelope_neg
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (hu : u ≤ 0) :
    ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (k : ℝ) ^ 2) :=
  shell_neg_tsum_le u hu κ' hκ'

/-- The absolute shell constant `∑'_k (k+1)e^{k/2}e^{-κ'k²}` is nonneg and finite. -/
theorem shell_const_nonneg (κ' : ℝ) (hκ' : 0 < κ') :
    0 ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (k : ℝ) ^ 2) := by
  apply tsum_nonneg
  intro k; positivity

/-- **A.ENV-DOM envelope, u≤0, final shape.** For `u ≤ 0`, the shell tsum is
bounded by `Kbound·(1 + u² + e^u)` where `Kbound` is the absolute shell constant,
since `1 + u² + e^u ≥ 1` and the tsum `≤ Kbound`. This is the `u≤0` half of the
envelope `V_∞^# ≤ C(1+u²+e^u)` (manuscript p.55). -/
theorem envelope_neg_final
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (hu : u ≤ 0) :
    ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ (∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (k : ℝ) ^ 2))
        * (1 + u ^ 2 + Real.exp u) := by
  have hKnn := shell_const_nonneg κ' hκ'
  have hneg := envelope_neg κ' hκ' u hu
  have henv1 : (1:ℝ) ≤ 1 + u ^ 2 + Real.exp u := by
    have : 0 < Real.exp u := Real.exp_pos _
    nlinarith [sq_nonneg u, this]
  calc ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (k : ℝ) ^ 2) := hneg
    _ = (∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (k : ℝ) ^ 2)) * 1 := (mul_one _).symm
    _ ≤ (∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
          * Real.exp (-κ' * (k : ℝ) ^ 2)) * (1 + u ^ 2 + Real.exp u) := by
        apply mul_le_mul_of_nonneg_left henv1 hKnn

#print axioms envelope_neg
#print axioms shell_const_nonneg
#print axioms envelope_neg_final

end RHFormalization
