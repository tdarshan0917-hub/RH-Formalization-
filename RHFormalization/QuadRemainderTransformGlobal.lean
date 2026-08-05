import RHFormalization.QuadMassFnContinuity
import RHFormalization.CompletedZetaGrowth

/-!
# RHFormalization.QuadRemainderTransformGlobal
**Ledger item 2 (subsuming the regime split): the GLOBAL transform bound.**
The t^{3/2} mass bound holds for all t > 0, so the full-line Laplace
transform of the quadratic remainder mass is bounded by
`Γ(5/2)·δ^{−5/2}·SupVConst²/√π` for `δ ≤ Re s`, via the banked
`integral_rpow_mul_exp_eq_gamma`. N-free, qs-uniform, Ω-compact-ready
through the compact's Re floor.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory Set

variable {N : ℕ}

/-- The global majorant is integrable on `Ioi 0`. -/
theorem integrableOn_rpow_exp_majorant {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ ((3:ℝ)/2) * Real.exp (-δ * t))
      (Ioi (0:ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := (3:ℝ)/2) (b := δ) (by norm_num) (by norm_num) hδ
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]

/-- **The global transform bound for the quadratic remainder mass.**
For `δ ≤ Re s`, `0 < δ`:
`‖∫₀^∞ e^{−st}·mass(t) dt‖ ≤ δ^{−5/2}·Γ(5/2)·SupVConst²/√π`. -/
theorem quadRemainder_transform_global_le (qs : Finset ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hRe : δ ≤ s.re)
    (hint : IntegrableOn (fun t : ℝ =>
        Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ))
      (Ioi (0:ℝ))) :
    ‖∫ t in Ioi (0:ℝ),
        Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ)‖
      ≤ δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2)
          * (SupVConst ^ 2 / Real.sqrt Real.pi) := by
  set C : ℝ := SupVConst ^ 2 / Real.sqrt Real.pi with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hpt : ∀ t ∈ Ioi (0:ℝ),
      ‖Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ)‖
        ≤ t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C := by
    intro t ht
    rw [norm_mul, Complex.norm_exp, Complex.norm_real]
    have hre : (-(s * (t:ℂ))).re = -(s.re * t) := by
      simp [Complex.mul_re]
    rw [hre]
    have hker : Real.exp (-(s.re * t)) ≤ Real.exp (-δ * t) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hRe (le_of_lt ht)
      linarith
    have hmass : ‖quadRemainderMassFn (N := N) qs t‖ ≤ t ^ ((3:ℝ)/2) * C := by
      rw [Real.norm_eq_abs]
      exact quadRemainderMassFn_abs_le qs hN t ht
    calc Real.exp (-(s.re * t)) * ‖quadRemainderMassFn (N := N) qs t‖
        ≤ Real.exp (-δ * t) * (t ^ ((3:ℝ)/2) * C) :=
          mul_le_mul hker hmass (norm_nonneg _) (Real.exp_pos _).le
      _ = t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C := by ring
  have hmajInt : IntegrableOn (fun t : ℝ =>
      t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C) (Ioi (0:ℝ)) :=
    (integrableOn_rpow_exp_majorant hδ).mul_const C
  have hbound : ‖∫ t in Ioi (0:ℝ),
      Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C := by
    refine norm_integral_le_of_norm_le hmajInt ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hpt t ht
  refine hbound.trans (le_of_eq ?_)
  have hgamma : ∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t)
      = δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2) := by
    have h := integral_rpow_mul_exp_eq_gamma
      (a := (5:ℝ)/2) (b := δ) (by norm_num) hδ
    rw [show ((5:ℝ)/2 - 1) = (3:ℝ)/2 by norm_num] at h
    rw [h]
    congr 1
    rw [show (-(5:ℝ)/2) = -((5:ℝ)/2) by norm_num]
  calc ∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C
      = (∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t)) * C := by
        first
          | exact MeasureTheory.integral_mul_const _ C
          | exact integral_mul_const _ C
          | exact MeasureTheory.integral_mul_right _ C
          | rw [MeasureTheory.integral_mul_const]
          | rw [integral_mul_const]
    _ = δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2) * C := by rw [hgamma]

#print axioms integrableOn_rpow_exp_majorant
#print axioms quadRemainder_transform_global_le

end

end RHFormalization
