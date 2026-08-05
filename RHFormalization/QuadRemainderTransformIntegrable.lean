import RHFormalization.QuadRemainderTransformGlobal

/-!
# RHFormalization.QuadRemainderTransformIntegrable
**Ledger item 2b: the hint discharge.** The transform integrand
`e^{−st}·quadRemainderMassFn t` is integrable on `Ioi 0` for `δ ≤ Re s`,
`0 < δ` — dominated by the banked majorant `t^{3/2}e^{−δt}·C` via
`Integrable.mono'` (donor skeleton: `integrableOn_t_cexp`). Unconditional
global transform bound follows.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory Set

variable {N : ℕ}

/-- **The hint discharge**: transform integrand integrable on `Ioi 0`. -/
theorem quadRemainderTransform_integrableOn (qs : Finset ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hRe : δ ≤ s.re) :
    IntegrableOn (fun t : ℝ =>
        Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ))
      (Ioi (0:ℝ)) := by
  set C : ℝ := SupVConst ^ 2 / Real.sqrt Real.pi with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hmajInt : IntegrableOn (fun t : ℝ =>
      t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C) (Ioi (0:ℝ)) :=
    (integrableOn_rpow_exp_majorant hδ).mul_const C
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ =>
        Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ))
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Continuous.aestronglyMeasurable
    exact ((Complex.continuous_exp).comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)).mul
      (Complex.continuous_ofReal.comp (continuous_quadRemainderMassFn qs))
  refine Integrable.mono' hmajInt hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
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

/-- **Unconditional global transform bound** — hint discharged. -/
theorem quadRemainder_transform_global_le' (qs : Finset ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hRe : δ ≤ s.re) :
    ‖∫ t in Ioi (0:ℝ),
        Complex.exp (-(s * t)) * ((quadRemainderMassFn (N := N) qs t : ℝ) : ℂ)‖
      ≤ δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2)
          * (SupVConst ^ 2 / Real.sqrt Real.pi) :=
  quadRemainder_transform_global_le qs hN δ hδ s hRe
    (quadRemainderTransform_integrableOn qs hN δ hδ s hRe)

#print axioms quadRemainderTransform_integrableOn
#print axioms quadRemainder_transform_global_le'

end

end RHFormalization
