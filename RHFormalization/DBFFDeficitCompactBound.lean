import RHFormalization.DBFFBcorrWindow
import RHFormalization.ShiftedLaplaceOmegaGeometry
import RHFormalization.MontelUniqueLimit

/-!
# DBFFDeficitCompactBound — window deficit on Ω-compacts, part 1

ROUTE CARD
1. Target: D.MR.2 window sector for the corrected provider (extends Brick A
   from RHP(1) into the parabola). Consumer: provider ε-field / D.MR.5.
2. Objects: BcorrWin (banked); kernel compact bound (new, this file).
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.CANONICAL-WINDOW / D.MR.5. 7. Next lemma (part 2): the
   weight-mass growth bound deficitWeightMass n · admR/(2admL) → 0, donors
   from EnvDomShellCount per scout.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- Positive lower bound for the kernel denominator on an Ω-compact. -/
theorem kernelDenom_min (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ K, c ≤ ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖ := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, one_pos, by simp [hemp]⟩
  · have hcont : ContinuousOn (fun s : ℂ => ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖) K := by
      apply ContinuousOn.norm
      apply ContinuousOn.mul continuousOn_const
      intro s hs
      have hslit : (s + (1/4:ℂ)) ∈ Complex.slitPlane :=
        shiftedLaplaceShift_mem_slitPlane_of_mem_Omega s (hKO hs)
      have h1 : ContinuousAt (fun z : ℂ => Complex.sqrt (z + (1/4:ℂ))) s := by
        first
          | exact ((Complex.continuousAt_sqrt hslit).comp
              (by fun_prop : ContinuousAt (fun z : ℂ => z + (1/4:ℂ)) s))
          | exact ContinuousAt.comp (Complex.continuousAt_sqrt hslit)
              (by fun_prop)
          | (have hd : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (z + (1/4:ℂ))) s := by
               have hsh : DifferentiableAt ℂ (fun z : ℂ => z + (1/4:ℂ)) s := by fun_prop
               simpa using (Complex.differentiableAt_sqrt hslit).comp s hsh
             exact hd.continuousAt)
      exact h1.continuousWithinAt
    obtain ⟨s₀, hs₀K, hs₀min⟩ := hK.exists_isMinOn hne hcont
    refine ⟨‖2 * Complex.sqrt (s₀ + (1/4:ℂ))‖, ?_, fun s hs => hs₀min hs⟩
    have hne0 : (s₀ + (1/4:ℂ)) ≠ 0 :=
      shiftedLaplaceShift_ne_zero_of_mem_Omega s₀ (hKO hs₀K)
    have hsq : (Complex.sqrt (s₀ + (1/4:ℂ)))^2 = s₀ + (1/4:ℂ) := by
      unfold Complex.sqrt
      exact Complex.cpow_nat_inv_pow _ (by norm_num)
    have hsqrt_ne : Complex.sqrt (s₀ + (1/4:ℂ)) ≠ 0 := by
      intro h0
      apply hne0
      rw [← hsq, h0]; ring
    have : (2:ℂ) * Complex.sqrt (s₀ + (1/4:ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) hsqrt_ne
    exact norm_pos_iff.mpr this

/-- Kernel bound on an Ω-compact: for `a ≥ 0`, `‖kernel a s‖ ≤ c⁻¹`. -/
theorem kernel_norm_le_on_compact
    {K : Set ℂ} {c : ℝ} (hc : 0 < c)
    (hcK : ∀ s ∈ K, c ≤ ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖)
    (hKO : K ⊆ Ω)
    (a : ℝ) (ha : 0 ≤ a) {s : ℂ} (hs : s ∈ K) :
    ‖shiftedLaplaceHeatKernelC a s‖ ≤ c⁻¹ := by
  unfold shiftedLaplaceHeatKernelC
  rw [norm_mul, Complex.norm_exp]
  have hre : 0 ≤ (Complex.sqrt (s + (1/4:ℂ))).re := sqrt_re_nonneg _
  have hexp : (-(a:ℂ) * Complex.sqrt (s + (1/4:ℂ))).re ≤ 0 := by
    rw [Complex.mul_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero]
    nlinarith [hre, ha]
  have h1 : ‖(1:ℂ) / (2 * Complex.sqrt (s + (1/4:ℂ)))‖ ≤ c⁻¹ := by
    rw [norm_div, norm_one]
    have hden := hcK s hs
    have hden0 : (0:ℝ) < ‖2 * Complex.sqrt (s + (1/4:ℂ))‖ := lt_of_lt_of_le hc hden
    rw [div_le_iff₀ hden0]
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    nlinarith [hden, hc.le]
  calc ‖(1:ℂ)/(2 * Complex.sqrt (s + (1/4:ℂ)))‖ * Real.exp ((-(a:ℂ) * Complex.sqrt (s + (1/4:ℂ))).re)
      ≤ c⁻¹ * 1 := by
        apply mul_le_mul h1 _ (Real.exp_nonneg _) (inv_nonneg.mpr hc.le)
        simpa using Real.exp_le_one_iff.mpr hexp
    _ = c⁻¹ := by ring

/-- Per-stage deficit weight mass (growth bound = part 2, after scout). -/
def deficitWeightMass (n : ℕ) : ℝ :=
  (activePrimePowerPairsCenterBelow (admR n)).sum fun q => ‖q.weightC‖

/-- **Deficit bound on Ω-compacts (part 1)**: mass-factored estimate. -/
theorem BcorrWin_norm_le_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ K,
      ‖BcorrWin n s‖ ≤ admR n / (2 * admL n) * deficitWeightMass n * C := by
  obtain ⟨c, hc, hcK⟩ := kernelDenom_min K hK hKO
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro n s hs
  have hL2 : (0 : ℝ) < 2 * admL n := by have := admL_pos' n; linarith
  have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
          shiftedLaplaceHeatKernelC q.center s‖ ≤
        admR n / (2 * admL n) * ‖q.weightC‖ * c⁻¹ := by
    intro q hq
    have hcle : q.center ≤ admR n :=
      ((activePrimePowerPairsCenterBelow_mem (admR n) q).mp hq).2
    have hfrac0 : (0 : ℝ) ≤ q.center / (2 * admL n) :=
      div_nonneg (center_nonneg q) hL2.le
    have hcnorm : ‖((q.center / (2 * admL n) : ℝ) : ℂ)‖ = q.center / (2 * admL n) := by
      first
        | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfrac0]
        | rw [Complex.norm_ofReal, abs_of_nonneg hfrac0]
    have hker := kernel_norm_le_on_compact hc hcK hKO q.center (center_nonneg q) hs
    have hfrac : q.center / (2 * admL n) ≤ admR n / (2 * admL n) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hcle (inv_nonneg.mpr hL2.le)
    calc ‖q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s‖
        = ‖q.weightC‖ * (q.center / (2 * admL n)) *
            ‖shiftedLaplaceHeatKernelC q.center s‖ := by
          rw [norm_mul, norm_mul, hcnorm]
      _ ≤ ‖q.weightC‖ * (admR n / (2 * admL n)) * c⁻¹ := by
          have hnn : (0:ℝ) ≤ ‖q.weightC‖ * (admR n / (2 * admL n)) := by
            apply mul_nonneg (norm_nonneg _)
            exact div_nonneg (admR_pos n).le hL2.le
          apply mul_le_mul _ hker (norm_nonneg _) hnn
          exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg _)
      _ = admR n / (2 * admL n) * ‖q.weightC‖ * c⁻¹ := by ring
  calc ‖BcorrWin n s‖
      ≤ (activePrimePowerPairsCenterBelow (admR n)).sum fun q =>
          ‖q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s‖ := norm_sum_le _ _
    _ ≤ (activePrimePowerPairsCenterBelow (admR n)).sum fun q =>
          admR n / (2 * admL n) * ‖q.weightC‖ * c⁻¹ :=
        Finset.sum_le_sum hterm
    _ = admR n / (2 * admL n) * deficitWeightMass n * c⁻¹ := by
        unfold deficitWeightMass
        rw [Finset.mul_sum, Finset.sum_mul]

#print axioms kernelDenom_min
#print axioms kernel_norm_le_on_compact
#print axioms BcorrWin_norm_le_on_compact

end

end RHFormalization
