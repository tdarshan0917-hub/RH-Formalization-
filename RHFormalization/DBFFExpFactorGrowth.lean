import RHFormalization.DBFFDecodedProfiles

/-!
# DBFFExpFactorGrowth — P2-2b: the stage exponential's exact growth rate

ROUTE CARD
1. Target: `‖bulkProfileExpFactor n s‖ ≤ exp(admR n / 2)` on ALL of Ω —
   the coefficient-side growth input for the D.BFF error control (P2-4).
   At the frozen schedule `exp(admR n / 2) = (n+2)^{1/4}`: polynomial,
   to be beaten by the expansion's decaying factors.
2. Mechanism: `Re √(s+1/4) ≥ 0` on all of ℂ (banked `sqrt_re_nonneg`),
   so `Re((1/2−w)·admR n) ≤ admR n / 2`.
3. Raw B on Ω? NO. B_stage − M targeted as a Prop? NO.
4. Consumer: P2-4 (ε control).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **P2-2b growth bound**: the stage exponential factor grows at most like
`exp(admR n / 2)` — everywhere on ℂ, in particular on Ω. -/
theorem bulkProfileExpFactor_norm_le (n : ℕ) (s : ℂ) :
    ‖bulkProfileExpFactor n s‖ ≤ Real.exp (admR n / 2) := by
  unfold bulkProfileExpFactor
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * ((admR n : ℝ) : ℂ)).re
      = ((1/2:ℝ) - (Complex.sqrt (s + (1/4:ℂ))).re) * admR n := by
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  have h0 : (0:ℝ) ≤ (Complex.sqrt (s + (1/4:ℂ))).re := sqrt_re_nonneg (s + (1/4:ℂ))
  have hR := admR_nonneg n
  nlinarith [h0, hR]

#print axioms bulkProfileExpFactor_norm_le

end

end RHFormalization
