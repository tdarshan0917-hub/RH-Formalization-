import RHFormalization.DenseCenteredObservable
import RHFormalization.PerSpikeTransformDefectBound
import RHFormalization.AdaptiveDefectStageBound
import RHFormalization.ResolventDenomCompactLowerBound
import RHFormalization.DBFFDeficitCompactBound
import RHFormalization.DenseCompactGaps
import RHFormalization.AdmissibleS1MassSqrt
import Mathlib

/-!
B(i)-6 part 1 (GPT-countersigned): F^ctr definition, integrability helper,
and the per-u majorant (the signed pointwise decomposition).

SIGNED decomposition: K_n(u,s) − K(u,s) = 2·D_n(u,s) − (u/L)·K(u,s), where
D_n = (1/2L)·spikeTransform − ((L−u)/2L)·K is the L1e defect. Hence
  ‖K_n(u,·) − K(u,·)‖ ≤ 2·perSpikeBound(R_n, L_n, N_n, c₀) + (u/L_n)·c₁⁻¹
with c₀ from resolventDenom_lower_bound (D4b convention) and c₁ from
kernelDenom_min — CONSTANTS KEPT SEPARATE per GPT amendment.

Rate (part 2): denseFctrRate n = x^{-1/8}(1+log x) + x^{-3/4}, x = n+2
(= O(X^{-1/4}logX + X^{-3/2}), X = √x; resolution term under the certified
L ≤ x³ ceiling ONLY — sharper exponent unclaimed per frozen ledger).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace RHFormalization

noncomputable section

open Complex Filter intervalIntegral

open scoped Topology BigOperators

/-- **F^ctr** (GPT-signed shape): the weighted centering defect integral. -/
def denseFctr (n : ℕ) (s : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..(admR n),
    ((Real.exp (u/2) : ℝ) : ℂ) *
      (denseKernelN n u s - shiftedLaplaceHeatKernelC u s)

/-- Continuity in `u` of the finite spike transform ON `[0, admR n]`:
each diagonal entry rewrites by the banked closed form
`TmatrixElement_diag_eval` ((L−a)/2·cos + L/(2kπ)·sin), continuous in the
center; indices are k+1 ≠ 0 and centers stay in [0, L). -/
theorem continuousOn_denseKernelN_u (n : ℕ) (s : ℂ) :
    ContinuousOn (fun u : ℝ => denseKernelN n u s)
      (Set.Icc (0:ℝ) (admR n)) := by
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  unfold denseKernelN
  apply ContinuousOn.mul continuousOn_const
  rw [show (fun u : ℝ => galerkinSpikeTransform (N := denseN n)
      (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s)
    = fun u : ℝ => ∑ m : Fin (denseN n),
        ((galerkinT (N := denseN n) (denseL n) u m m : ℝ) : ℂ) *
          (1 / (s + (1/4 : ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ)))
    from funext fun u => galerkinSpikeTransform_eq_diag_pairing n u s]
  apply continuousOn_finsetSum
  intro m _
  apply ContinuousOn.mul _ continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  have hentry : ∀ u ∈ Set.Icc (0:ℝ) (admR n),
      galerkinT (N := denseN n) (denseL n) u m m
        = (2 / denseL n) *
            ((denseL n - u) / 2
              * Real.cos ((((m:ℕ)+1 : ℕ) : ℝ) * Real.pi * u / denseL n)
            + denseL n / (2 * (((m:ℕ)+1 : ℕ) : ℝ) * Real.pi)
              * Real.sin ((((m:ℕ)+1 : ℕ) : ℝ) * Real.pi * u / denseL n)) := by
    intro u hu
    show (2 / denseL n) * TmatrixElement (denseL n) u ((m:ℕ)+1) ((m:ℕ)+1) = _
    rw [TmatrixElement_diag_eval (denseL n) u hL0 hu.1
      (le_of_lt (lt_of_le_of_lt hu.2 (admR_lt_denseL n)))
      ((m:ℕ)+1) (Nat.succ_ne_zero _)]
  apply ContinuousOn.congr _ hentry
  apply Continuous.continuousOn
  fun_prop

/-- Continuity in `u ≥ 0`-free form: the continuum kernel is continuous in
the center variable (exp of a continuous function times a constant). -/
theorem continuous_kernel_u (s : ℂ) :
    Continuous (fun u : ℝ => shiftedLaplaceHeatKernelC u s) := by
  unfold shiftedLaplaceHeatKernelC
  apply Continuous.mul continuous_const
  apply Complex.continuous_exp.comp
  first
    | fun_prop
    | (apply Continuous.mul _ continuous_const
       exact (Complex.continuous_ofReal.comp continuous_id).neg)

/-- **GPT Amendment 2 — the named integrability helper.** -/
theorem denseFctr_integrand_intervalIntegrable (n : ℕ) (s : ℂ) :
    IntervalIntegrable
      (fun u : ℝ => ((Real.exp (u/2) : ℝ) : ℂ) *
        (denseKernelN n u s - shiftedLaplaceHeatKernelC u s))
      MeasureTheory.volume 0 (admR n) := by
  have hR0 : (0:ℝ) ≤ admR n := (admR_pos n).le
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hR0]
  apply ContinuousOn.mul
  · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_id.div_const 2))).continuousOn
  · exact (continuousOn_denseKernelN_u n s).sub
      (continuous_kernel_u s).continuousOn

/-- **The signed per-u majorant** (GPT deliverable 4): for `u ∈ [0, admR n]`,
`s ∈ K ⋐ Ω`, with c₀ the resolvent floor and c₁ the kernel-denominator floor,
`‖K_n(u,s) − K(u,s)‖ ≤ 2·perSpikeBound(admR n, denseL n, denseN n, c₀)
  + (u/denseL n)·c₁⁻¹`. -/
theorem denseKernelN_sub_kernel_norm_le
    (n : ℕ) {K : Set ℂ} (hKΩ : K ⊆ Ω)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hfl : ∀ s ∈ K, ∀ ξ : ℝ, c₀ * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hc₁K : ∀ s ∈ K, c₁ ≤ ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖)
    {s : ℂ} (hs : s ∈ K) {u : ℝ} (hu0 : 0 ≤ u) (huR : u ≤ admR n) :
    ‖denseKernelN n u s - shiftedLaplaceHeatKernelC u s‖
      ≤ 2 * perSpikeBound (admR n) (denseL n) (denseN n) c₀
        + (u / denseL n) * c₁⁻¹ := by
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have hN0 : 0 < denseN n := by
    show 0 < admN n
    unfold admN
    positivity
  have huL : u ≤ denseL n := le_of_lt (lt_of_le_of_lt huR (admR_lt_denseL n))
  -- the algebraic decomposition K_n − K = 2·D_n − (u/L)·K
  have hdecomp : denseKernelN n u s - shiftedLaplaceHeatKernelC u s
      = 2 * (((1 / (2 * denseL n) : ℝ) : ℂ)
            * galerkinSpikeTransform (N := denseN n)
                (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s
          - (((denseL n - u) / (2 * denseL n) : ℝ) : ℂ)
            * shiftedLaplaceHeatKernelC u s)
        - ((u / denseL n : ℝ) : ℂ) * shiftedLaplaceHeatKernelC u s := by
    unfold denseKernelN
    have hLne : (denseL n : ℝ) ≠ 0 := hL0.ne'
    have h1 : ((1 / denseL n : ℝ) : ℂ)
        = 2 * ((1 / (2 * denseL n) : ℝ) : ℂ) := by
      push_cast
      field_simp
    have h2 : (2 : ℂ) * (((denseL n - u) / (2 * denseL n) : ℝ) : ℂ)
        + ((u / denseL n : ℝ) : ℂ) = 1 := by
      have hLC : ((denseL n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLne
      push_cast
      field_simp
      try ring
    calc ((1 / denseL n : ℝ) : ℂ)
          * galerkinSpikeTransform (N := denseN n)
              (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s
        - shiftedLaplaceHeatKernelC u s
        = 2 * ((1 / (2 * denseL n) : ℝ) : ℂ)
            * galerkinSpikeTransform (N := denseN n)
                (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s
          - (2 * (((denseL n - u) / (2 * denseL n) : ℝ) : ℂ)
              + ((u / denseL n : ℝ) : ℂ)) * shiftedLaplaceHeatKernelC u s := by
          rw [h1, h2]
          ring
      _ = _ := by ring
  rw [hdecomp]
  -- triangle inequality then the two banked bounds
  have hL1e := perSpikeTransformDefect_norm_le (N := denseN n) hN0
    (denseL n) u hL0 hu0 huL s (hKΩ hs) c₀ hc₀ (hfl s hs)
  have hmono := perSpikeBound_mono_center u (admR n) (denseL n)
    (denseN n) c₀ hc₀ hL0 huR
  have hDn : ‖((1 / (2 * denseL n) : ℝ) : ℂ)
        * galerkinSpikeTransform (N := denseN n)
            (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s
      - (((denseL n - u) / (2 * denseL n) : ℝ) : ℂ)
        * shiftedLaplaceHeatKernelC u s‖
      ≤ perSpikeBound (admR n) (denseL n) (denseN n) c₀ :=
    le_trans hL1e hmono
  have hker : ‖shiftedLaplaceHeatKernelC u s‖ ≤ c₁⁻¹ :=
    kernel_norm_le_on_compact hc₁ hc₁K hKΩ u hu0 hs
  have hfrac0 : (0:ℝ) ≤ u / denseL n := div_nonneg hu0 hL0.le
  calc ‖2 * (((1 / (2 * denseL n) : ℝ) : ℂ)
          * galerkinSpikeTransform (N := denseN n)
              (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s
        - (((denseL n - u) / (2 * denseL n) : ℝ) : ℂ)
          * shiftedLaplaceHeatKernelC u s)
      - ((u / denseL n : ℝ) : ℂ) * shiftedLaplaceHeatKernelC u s‖
      ≤ ‖(2:ℂ) * (((1 / (2 * denseL n) : ℝ) : ℂ)
            * galerkinSpikeTransform (N := denseN n)
                (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s
          - (((denseL n - u) / (2 * denseL n) : ℝ) : ℂ)
            * shiftedLaplaceHeatKernelC u s)‖
        + ‖((u / denseL n : ℝ) : ℂ) * shiftedLaplaceHeatKernelC u s‖ :=
        norm_sub_le _ _
    _ ≤ 2 * perSpikeBound (admR n) (denseL n) (denseN n) c₀
        + (u / denseL n) * c₁⁻¹ := by
        apply add_le_add
        · rw [norm_mul]
          have h2 : ‖(2:ℂ)‖ = 2 := by simp
          rw [h2]
          exact mul_le_mul_of_nonneg_left hDn (by norm_num)
        · rw [norm_mul]
          have hcast : ‖((u / denseL n : ℝ) : ℂ)‖ = u / denseL n := by
            first
              | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfrac0]
              | rw [Complex.norm_ofReal, abs_of_nonneg hfrac0]
          rw [hcast]
          exact mul_le_mul_of_nonneg_left hker hfrac0

#print axioms denseFctr
#print axioms continuousOn_denseKernelN_u
#print axioms continuous_kernel_u
#print axioms denseFctr_integrand_intervalIntegrable
#print axioms denseKernelN_sub_kernel_norm_le

end

end RHFormalization
