import RHFormalization.DBFFCompensator
import Mathlib

/-!
# DBFFCompensatorMainTerm — D.OP.2 pivot: M_α = truncated Stieltjes main term

ROUTE CARD
1. Target: the identity D.OP.2 pivots on — compensatorM equals the truncated
   main-term integral ∫₀^{admR} e^{(1/2−w)t}dt (i.e. ∫₁^{e^R} x^{−1/2−w}dx
   under x = eᵗ) plus the fixed term (1/2−w)⁻¹, all times (2w)⁻¹. Makes
   B_stage − M_α literally the Stieltjes error object of (★).
2. Objects: `compensatorM` (banked), `sqrt_ne_half` (banked),
   Mathlib `integral_exp_mul_complex`.
3. Raw B on Ω? NO. 4. R = F − raw B forced? NO. 5. True outright.
6. Manuscript: D.OP-BOUND, Lemma D.OP.2 (main-term normalization).
7. Consumer: discrete-vs-integral comparison brick; O3 restatement in t-form.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex intervalIntegral

/-- The truncated main-term integral `∫₀^{admR n} e^{(1/2−√(s+1/4))t} dt`
(the Stieltjes main term `∫₁^{e^{admR n}} x^{−1/2−√(s+1/4)} dx` after x = eᵗ). -/
def mainTermIntegral (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..(admR n),
    Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * (t : ℂ))

/-- Evaluation of the truncated main-term integral on Ω. -/
theorem mainTermIntegral_eval (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    mainTermIntegral n s
      = (Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))
            * ((admR n : ℝ) : ℂ)) - 1)
          / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  have hc : ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) ≠ 0 := by
    first
      | exact sub_ne_zero_of_ne (Ne.symm (sqrt_ne_half hs))
      | exact sub_ne_zero.mpr (Ne.symm (sqrt_ne_half hs))
      | exact sub_ne_zero.mpr ((sqrt_ne_half hs).symm)
  unfold mainTermIntegral
  first
    | (rw [integral_exp_mul_complex hc]
       simp [Complex.exp_zero])
    | (rw [intervalIntegral.integral_exp_mul_complex hc]
       simp [Complex.exp_zero])
    | (rw [integral_exp_mul_complex hc]
       norm_num)
    | (rw [intervalIntegral.integral_exp_mul_complex hc]
       norm_num)

/-- **D.OP.2 pivot**: on Ω, the compensator IS the truncated Stieltjes main
term plus the fixed holomorphic constant, normalized by `(2√(s+1/4))⁻¹`. -/
theorem compensatorM_eq_mainTerm (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    compensatorM n s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) *
          (mainTermIntegral n s
            + 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))) := by
  rw [mainTermIntegral_eval n hs]
  unfold compensatorM
  first
    | rw [div_add_div_same, sub_add_cancel]
    | rw [div_add_div_same, sub_add_cancel_right]
    | (rw [div_add_div_same]
       norm_num)
    | (have hc : ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) ≠ 0 := by
         first
           | exact sub_ne_zero_of_ne (Ne.symm (sqrt_ne_half hs))
           | exact sub_ne_zero.mpr ((sqrt_ne_half hs).symm)
       field_simp
       ring)

#print axioms mainTermIntegral
#print axioms mainTermIntegral_eval
#print axioms compensatorM_eq_mainTerm

end

end RHFormalization
