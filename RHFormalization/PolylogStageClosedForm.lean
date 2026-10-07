import RHFormalization.U4ZeroVisibilityAbel
import RHFormalization.DBFFCompensatorMainTerm
import RHFormalization.PolylogWeightSummable
import Mathlib

/-!
# PolylogStageClosedForm — PL-3: the stage-`M²−2` star object in closed form

At `n = M² − 2` the cutoff is `⌊e^{admR n}⌋ = M` and `admR n = log M`, so on `Ω`
`starObject (M²−2) s = Σ_{k≤M} Λ(k) k^{−ρ_s} − M^{1−ρ_s}/(1−ρ_s)`, `ρ_s := √(s+¼)+½`.
Pure rewriting through the banked `mainTermIntegral_eval` and
`admR_square_cutoff_realizes_nat`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

theorem admR_square_stage_eq_log (M : ℕ) (hM : 2 ≤ M) :
    admR (M ^ 2 - 2) = Real.log (M : ℝ) := by
  have hexp : Real.exp (admR (M ^ 2 - 2)) = (M : ℝ) := by
    rw [exp_admR]
    have hsq : 2 ≤ M ^ 2 := by nlinarith
    have hnat : M ^ 2 - 2 + 2 = M ^ 2 := Nat.sub_add_cancel hsq
    have harg : (((M ^ 2 - 2 : ℕ) : ℝ) + 2) = (M : ℝ) ^ 2 := by exact_mod_cast hnat
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  rw [← hexp, Real.log_exp]

/-- The stage exponential at `n = M²−2` is the complex power `M^c`. -/
theorem exp_mul_admR_square_stage (M : ℕ) (hM : 2 ≤ M) (c : ℂ) :
    Complex.exp (c * ((admR (M ^ 2 - 2) : ℝ) : ℂ)) = (M : ℂ) ^ c := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hlog : ((Real.log (M : ℝ) : ℝ) : ℂ) = Complex.log (M : ℂ) := by
    first
      | exact Complex.natCast_log
      | (rw [Complex.ofReal_log (Nat.cast_nonneg M)]; norm_cast; done)
      | (rw [Complex.ofReal_log (Nat.cast_nonneg M)]; simp; done)
      | (rw [Complex.ofReal_log (Nat.cast_nonneg M)]; push_cast; rfl)
  rw [admR_square_stage_eq_log M hM, hlog, Complex.cpow_def_of_ne_zero hM0, mul_comm]

/-- **PL-3**: closed form of the stage-`M²−2` star object on `Ω`. -/
theorem starObject_square_stage_closed (M : ℕ) (hM : 2 ≤ M) {s : ℂ} (hs : s ∈ Ω) :
    starObject (M ^ 2 - 2) s
      = (∑ k ∈ Finset.Ioc 0 M,
            LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k)
        - (M : ℂ) ^ ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))
            / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  have hc : ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (sqrt_ne_half hs))
  unfold starObject
  rw [admR_square_cutoff_realizes_nat M hM, mainTermIntegral_eval _ hs,
    exp_mul_admR_square_stage M hM]
  field_simp
  ring

#print axioms starObject_square_stage_closed

end

end RHFormalization
