import RHFormalization.GalerkinStieltjesRep
import RHFormalization.GalerkinSpikeShortTimeBound
import RHFormalization.DTailPerturbedTraceDomination
import RHFormalization.AdmissiblePrimeStageIdentity
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import RHFormalization.AdmissibleEigenvalueFloor
import Mathlib

/-!
# GalerkinHeadBound — pointwise short-time bounds on the Stieltjes integrand

ROUTE CARD
1. Target: `‖galQResIntegrand n s t‖ ≤ e^{-Re(s)·t} · (freeHeatDiagonal t + C)`,
   uniformly in `n`, for `t ∈ (0, spikeT0]`. This is the pointwise input to the
   head integral `∫₀^{t₀}` of the genuine Galerkin Stieltjes representation.
2. Objects: `galQResIntegrand = galFIntegrand - galBIntegrand` (GalerkinStieltjesRep).
   F-sector consumes `h_fk_perturbed_galerkin` (banked heat-trace domination).
   B-sector consumes `spike_sum_short_time_bound` (banked, n- and t-uniform).
3. Raw B on Ω? NO. 4. R = F − raw B? NO — this is the genuine `R_stage`. 5. True outright.
6. Manuscript: D.KEY-FORM, the truncated transform `∫₀^{t₀}`.
7. Consumer: the head integral bound; thence `DBFFO3ParabolaDepthHstar`.

NOTE. `admDensityC n = 1/(2·admL n)` is exactly the prefactor of
`h_fk_perturbed_galerkin`. The `(2/L)` normalization lives inside `galerkinV`,
not here, so no constant tracking is required.

NOTE. The `(4πt)^{-1/2}` singularity survives only in the F-sector, where it is
`freeHeatDiagonal t`, integrable at `0`. The B-sector is bounded outright: the
prefactor was already absorbed by `sqrt_inv_mul_exp_neg_div_le`.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex
open scoped BigOperators

/-- **F-SECTOR.** The perturbed heat trace, damped. Uniform in `n`, all `t > 0`. -/
theorem galF_integrand_norm_le (n : ℕ) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖galFIntegrand n s t‖ ≤ Real.exp (-s.re * t) * freeHeatDiagonal t := by
  have hL : 0 < admL n := by unfold admL; positivity
  have hfk := h_fk_perturbed_galerkin (N := admN n)
    (activePrimePowerCodesCenterBelow (admR n)) (admL n) t hL ht
    (galerkinVC_isHermitian (N := admN n) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
  have hdc : ‖admDensityC n‖ = 1 / (2 * admL n) := by
    unfold admDensityC
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsv : Real.exp (-SupVConst * t) ≤ 1 := by
    have := SupVConst_nonneg_adm
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hterm : ∀ i : Fin (admN n),
      ‖Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ))‖
        = Real.exp (-s.re * t) * Real.exp (-SupVConst * t)
            * Real.exp (-t * admPerturbedLam n i) := by
    intro i
    rw [Complex.norm_exp, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im]
    try ring
  unfold galFIntegrand
  rw [norm_mul, hdc]
  calc (1 / (2 * admL n)) * ‖∑ i : Fin (admN n),
          Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ))‖
      ≤ (1 / (2 * admL n)) * ∑ i : Fin (admN n),
          ‖Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ))‖ := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (1 / (2 * admL n)) * ∑ i : Fin (admN n),
          (Real.exp (-s.re * t) * Real.exp (-SupVConst * t))
            * Real.exp (-t * admPerturbedLam n i) := by
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hterm i]; try ring
    _ = (Real.exp (-s.re * t) * Real.exp (-SupVConst * t))
          * ((1 / (2 * admL n)) * ∑ i : Fin (admN n),
              Real.exp (-t * admPerturbedLam n i)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ (Real.exp (-s.re * t) * 1) * freeHeatDiagonal t := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsv (Real.exp_pos _).le
        · exact hfk
        · positivity
        · positivity
    _ = Real.exp (-s.re * t) * freeHeatDiagonal t := by ring

/-- **B-SECTOR.** The spike sum, damped. Uniform in `n` and in `t ∈ (0, spikeT0]`.
No `(4πt)^{-1/2}` survives here. -/
theorem galB_integrand_short_time_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (s : ℂ) (t : ℝ), 0 < t → t ≤ spikeT0 →
      ‖galBIntegrand n s t‖ ≤ Real.exp (-s.re * t) * C := by
  obtain ⟨C, hC0, hC⟩ := spike_sum_short_time_bound
  refine ⟨C, hC0, ?_⟩
  intro n s t ht ht0
  have he1 : ‖Complex.exp (-s * (t:ℂ))‖ = Real.exp (-s.re * t) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
  have he2 : ‖Complex.exp (-(t:ℂ)/4)‖ = Real.exp (-t/4) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.neg_re, Complex.neg_im, Complex.ofReal_re]
  have h4 : Real.exp (-t/4) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; linarith
  unfold galBIntegrand
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC * shiftedHeatIntegrand q.center s t‖
        ≤ Real.exp (-s.re * t) * (‖q.weightC‖ * ‖heatKernelG t q.center‖) := by
    intro q _
    unfold shiftedHeatIntegrand
    rw [norm_mul, norm_mul, norm_mul, he1, he2]
    have hw : (0:ℝ) ≤ ‖q.weightC‖ := norm_nonneg _
    have hg : (0:ℝ) ≤ ‖heatKernelG t q.center‖ := norm_nonneg _
    calc ‖q.weightC‖ * (Real.exp (-s.re * t) * Real.exp (-t/4)
            * ‖heatKernelG t q.center‖)
        = (Real.exp (-s.re * t) * (‖q.weightC‖ * ‖heatKernelG t q.center‖))
            * Real.exp (-t/4) := by ring
      _ ≤ (Real.exp (-s.re * t) * (‖q.weightC‖ * ‖heatKernelG t q.center‖)) * 1 :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = Real.exp (-s.re * t) * (‖q.weightC‖ * ‖heatKernelG t q.center‖) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hC n t ht ht0) (Real.exp_pos _).le

/-- **THE HEAD INTEGRAND BOUND.** `n`-uniform on `(0, spikeT0]`. The only
`t`-singularity is `freeHeatDiagonal t = (4πt)^{-1/2}`, which is integrable at `0`.
No half-plane hypothesis on `s`: this holds for every `s : ℂ`. -/
theorem galQRes_integrand_short_time_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (s : ℂ) (t : ℝ), 0 < t → t ≤ spikeT0 →
      ‖galQResIntegrand n s t‖
        ≤ Real.exp (-s.re * t) * (freeHeatDiagonal t + C) := by
  obtain ⟨C, hC0, hCB⟩ := galB_integrand_short_time_bound
  refine ⟨C, hC0, ?_⟩
  intro n s t ht ht0
  unfold galQResIntegrand
  refine le_trans (norm_sub_le _ _) ?_
  have hF := galF_integrand_norm_le n s t ht
  have hB := hCB n s t ht ht0
  calc ‖galFIntegrand n s t‖ + ‖galBIntegrand n s t‖
      ≤ Real.exp (-s.re * t) * freeHeatDiagonal t + Real.exp (-s.re * t) * C :=
        add_le_add hF hB
    _ = Real.exp (-s.re * t) * (freeHeatDiagonal t + C) := by ring

#print axioms galF_integrand_norm_le
#print axioms galB_integrand_short_time_bound
#print axioms galQRes_integrand_short_time_bound

end RHFormalization
