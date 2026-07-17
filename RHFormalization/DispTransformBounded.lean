import RHFormalization.DispIntegrandIntegrable
import Mathlib

/-!
# D.DISP-3 transform boundedness (manuscript p175)

The displacement-sector Laplace transform `∫₀^{t₀} e^{-st}·g(t) dt` is bounded by
`e^{σ₀·t₀}·∫₀^{t₀} g`, uniform for `Re s ≥ -σ₀`. On compact `K ⊂ Ω`, `Re s` is
bounded below, giving `sup_{s∈K} |transform| < ∞` (D.DISP-3) — displacement sector
locally bounded, the input the normal-family passage of D.CAN-REM consumes.

Backwards from RH: {R_α} locally bounded ⟸ displacement sector bounded ⟸ this.
-/

namespace RHFormalization
open Real MeasureTheory intervalIntegral

/-- **D.DISP-3 transform boundedness.** -/
theorem disp_transform_bounded
    (g : ℝ → ℝ) (t₀ σ₀ : ℝ) (ht₀ : 0 < t₀) (hσ₀ : 0 ≤ σ₀)
    (hg_nonneg : ∀ t ∈ Set.Icc (0:ℝ) t₀, 0 ≤ g t)
    (hg_int : IntervalIntegrable g volume 0 t₀)
    (s : ℂ) (hs : -σ₀ ≤ s.re) :
    ‖∫ t in (0:ℝ)..t₀, Complex.exp (-s * (t : ℂ)) * (g t : ℂ)‖
      ≤ Real.exp (σ₀ * t₀) * ∫ t in (0:ℝ)..t₀, g t := by
  refine (intervalIntegral.norm_integral_le_integral_norm ht₀.le).trans ?_
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) t₀,
      ‖Complex.exp (-s * (t : ℂ)) * (g t : ℂ)‖ ≤ Real.exp (σ₀ * t₀) * g t := by
    intro t ht
    obtain ⟨ht0, htt0⟩ := ht
    have hgt : 0 ≤ g t := hg_nonneg t ⟨ht0, htt0⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgt]
    have hnorm : ‖Complex.exp (-s * (t : ℂ))‖ = Real.exp (-(s.re) * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
            Complex.ofReal_im]
    rw [hnorm]
    apply mul_le_mul_of_nonneg_right _ hgt
    apply Real.exp_le_exp.mpr
    have h1 : -(s.re) ≤ σ₀ := by linarith
    calc -(s.re) * t ≤ σ₀ * t := mul_le_mul_of_nonneg_right h1 ht0
      _ ≤ σ₀ * t₀ := mul_le_mul_of_nonneg_left htt0 hσ₀
  have hb_int : IntervalIntegrable (fun t => Real.exp (σ₀ * t₀) * g t) volume 0 t₀ :=
    hg_int.const_mul _
  -- the norm integrand ‖e^{-st}·g‖ = ‖e^{-st}‖·|g| is integrable:
  -- |g| is integrable (hg_int.norm), ‖e^{-st}‖ is continuous; use mul_continuousOn.
  have hgabs_int : IntervalIntegrable (fun t : ℝ => ‖g t‖) volume 0 t₀ := hg_int.norm
  have hexp_cont : Continuous (fun t : ℝ => ‖Complex.exp (-s * (t:ℂ))‖) := by
    apply Continuous.norm
    apply Complex.continuous_exp.comp
    exact continuous_const.mul Complex.continuous_ofReal
  have hcont_exp : ContinuousOn (fun t : ℝ => ‖Complex.exp (-s * (t:ℂ))‖) (Set.uIcc 0 t₀) :=
    hexp_cont.continuousOn
  have hmeas_int' : IntervalIntegrable
      (fun t : ℝ => ‖g t‖ * ‖Complex.exp (-s * (t:ℂ))‖) volume 0 t₀ :=
    hgabs_int.mul_continuousOn hcont_exp
  have hfun_eq : (fun t : ℝ => ‖Complex.exp (-s * (t : ℂ)) * (g t : ℂ)‖)
      = (fun t : ℝ => ‖g t‖ * ‖Complex.exp (-s * (t:ℂ))‖) := by
    funext t
    rw [norm_mul, Complex.norm_real, mul_comm]
  have hmeas_int : IntervalIntegrable
      (fun t : ℝ => ‖Complex.exp (-s * (t : ℂ)) * (g t : ℂ)‖) volume 0 t₀ := by
    rw [hfun_eq]; exact hmeas_int'
  calc ∫ t in (0:ℝ)..t₀, ‖Complex.exp (-s * (t:ℂ)) * (g t : ℂ)‖
      ≤ ∫ t in (0:ℝ)..t₀, Real.exp (σ₀ * t₀) * g t :=
        integral_mono_on ht₀.le hmeas_int hb_int hpt
    _ = Real.exp (σ₀ * t₀) * ∫ t in (0:ℝ)..t₀, g t :=
        intervalIntegral.integral_const_mul _ _

#print axioms disp_transform_bounded

end RHFormalization
