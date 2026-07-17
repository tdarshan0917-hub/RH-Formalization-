import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RHFormalization

open MeasureTheory Real Set Complex HurwitzZeta Asymptotics Filter

/-- **G1: `f_modif` of the Hurwitz even pair at `a = 0` has exponential decay at `+∞`.**
Extracted from `isBigO_atTop_evenKernel_sub`. For `t > 1`, `f_modif t = ofReal (evenKernel 0 t) - 1`,
whose norm matches the real decay. -/
theorem fmodif_isBigO_exp :
    ∃ p : ℝ, 0 < p ∧
      (hurwitzEvenFEPair 0).f_modif =O[atTop] (fun t => Real.exp (-p * t)) := by
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  refine ⟨p, hp, ?_⟩
  -- reduce hp' to a clean `- 1` form (the `if 0 = 0` evaluates to 1)
  have hp1 : (fun x => evenKernel 0 x - 1) =O[atTop] fun x => rexp (-p * x) := by
    have : (fun x => evenKernel 0 x - if (0:UnitAddCircle) = 0 then (1:ℝ) else 0)
        = (fun x => evenKernel 0 x - 1) := by simp
    rwa [this] at hp'
  -- f_modif t =ᶠ ofReal (evenKernel 0 t - 1) for t > 1
  have hev : (hurwitzEvenFEPair 0).f_modif
      =ᶠ[atTop] (fun t => ((evenKernel 0 t - 1 : ℝ) : ℂ)) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    have hnotin : t ∉ Set.Ioo (0:ℝ) 1 := by
      simp only [Set.mem_Ioo, not_and, not_lt]; intro _; linarith
    simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Pi.add_apply,
      Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
      Set.indicator_of_notMem hnotin, Function.comp_apply, add_zero,
      ofReal_sub, ofReal_one]
    norm_num
  refine hev.trans_isBigO ?_
  rw [isBigO_norm_left.symm]
  simp only [Complex.norm_real]
  exact isBigO_norm_left.mpr hp1

#print axioms fmodif_isBigO_exp


/-- **G2: explicit pointwise exponential bound on `f_modif`.** From the `IsBigO` of G1, extract
a constant `C ≥ 0` and threshold `T₀` with `‖f_modif t‖ ≤ C · exp(-p·t)` for all `t ≥ T₀`.
The `setIntegral` comparison in G3 uses this to bound the Mellin integral by a Gamma integral. -/
theorem fmodif_exp_bound :
    ∃ (p C T₀ : ℝ), 0 < p ∧ 0 ≤ C ∧
      ∀ t, T₀ ≤ t → ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := fmodif_isBigO_exp
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  -- hC : ∀ᶠ t in atTop, ‖f_modif t‖ ≤ C * ‖exp (-p t)‖
  rw [Filter.eventually_atTop] at hC
  obtain ⟨T₀, hT₀⟩ := hC
  refine ⟨p, max C 0, T₀, hp, le_max_right _ _, fun t ht => ?_⟩
  have h := hT₀ t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
  calc ‖(hurwitzEvenFEPair 0).f_modif t‖
      ≤ C * Real.exp (-p * t) := h
    _ ≤ max C 0 * Real.exp (-p * t) := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

#print axioms fmodif_exp_bound

end RHFormalization
