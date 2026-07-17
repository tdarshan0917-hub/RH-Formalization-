import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Real Set Complex HurwitzZeta

namespace RHFormalization

/-- **Mellin triangle inequality.** The norm of a Mellin transform at `s` is bounded by the
Mellin transform of the norm at `re s`: `‖mellin f s‖ ≤ ∫ t in Ioi 0, t^(re s - 1) * ‖f t‖`.
Crucially the RHS depends only on `re s`, NOT on `im s` — this is the source of uniform-in-T
bounds on vertical lines. Same technique as the Γ-bound brick: `norm_integral_le_integral_norm`
plus `norm_cpow_eq_rpow_re_of_pos`. -/
theorem norm_mellin_le {f : ℝ → ℂ} {s : ℂ} :
    ‖mellin f s‖ ≤ ∫ t in Ioi (0:ℝ), t ^ (s.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  apply le_of_eq
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have htpos : (0:ℝ) < t := ht
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos htpos, Complex.sub_re, Complex.one_re]

#print axioms norm_mellin_le

/-- **Λ₀ of a WeakFEPair is bounded by a real-part-only integral.** Since `Λ₀ = mellin f_modif`,
the Mellin triangle inequality gives a bound depending only on `re s` — hence **uniform in
`im s`** on each vertical line. This is the key T-independence for vertical growth. -/
theorem norm_Lambda0_le (P : WeakFEPair ℂ) (s : ℂ) :
    ‖P.Λ₀ s‖ ≤ ∫ t in Ioi (0:ℝ), t ^ (s.re - 1) * ‖P.f_modif t‖ := by
  show ‖mellin P.f_modif s‖ ≤ _
  exact norm_mellin_le

#print axioms norm_Lambda0_le

/-- **The completed Riemann zeta `Λ₀` (entire) is bounded by a real-part-only integral.**
Specializing `norm_Lambda0_le` to `hurwitzEvenFEPair 0` at `s/2`: `completedRiemannZeta₀ s`
is bounded by an integral depending only on `re s` (via `re (s/2) = s.re/2`), hence **uniform
in `im s`** on each vertical line. -/
theorem norm_completedRiemannZeta0_le (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤
      (∫ t in Ioi (0:ℝ), t ^ (s.re / 2 - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) / 2 := by
  have heq : completedRiemannZeta₀ s = ((hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2 := rfl
  rw [heq, norm_div, Complex.norm_two]
  have hb := norm_Lambda0_le (hurwitzEvenFEPair 0) (s / 2)
  have hre : (s / 2).re = s.re / 2 := by rw [Complex.div_ofNat_re]
  rw [hre] at hb
  exact div_le_div_of_nonneg_right hb (by norm_num)
  
#print axioms norm_completedRiemannZeta0_le

/-- **Λ (completedRiemannZeta) bounded by its Λ₀ plus pole terms.** Via
`Λ = Λ₀ - 1/s - 1/(1-s)` and the triangle inequality. Combined with the T-uniform `Λ₀` bound,
this controls `‖Λ(σ+iT)‖` on vertical lines (the pole terms are bounded off `s = 0, 1`). -/
theorem norm_completedRiemannZeta_le (s : ℂ) :
    ‖completedRiemannZeta s‖ ≤ ‖completedRiemannZeta₀ s‖ + 1 / ‖s‖ + 1 / ‖1 - s‖ := by
  rw [completedRiemannZeta_eq s]
  calc ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖
      ≤ ‖completedRiemannZeta₀ s - 1 / s‖ + ‖1 / (1 - s)‖ := norm_sub_le _ _
    _ ≤ ‖completedRiemannZeta₀ s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := by
        gcongr; exact norm_sub_le _ _
    _ = ‖completedRiemannZeta₀ s‖ + 1 / ‖s‖ + 1 / ‖1 - s‖ := by
        rw [norm_div, norm_div, norm_one]

#print axioms norm_completedRiemannZeta_le

end RHFormalization
