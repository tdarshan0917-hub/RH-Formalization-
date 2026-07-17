import Mathlib.Analysis.Complex.JensenFormula
import RHFormalization.CompletedZetaGrowth
import RHFormalization.CompletedZetaMeromorphic
import RHFormalization.Basic
import RHFormalization.DefaultZeroMultiplicity
import RHFormalization.ZetaZeroBandFinite
import RHFormalization.HsumFromBandCount
import RHFormalization.Basic
import RHFormalization.DefaultZeroMultiplicity

/-!
# The xi-type entire function `ξ(s) = s(s-1)Λ₀(s) + 1`

`Λ₀ = completedRiemannZeta₀` does NOT vanish at nontrivial zeta zeros (there
`Λ₀(ρ) = 1/(ρ(1-ρ)) ≠ 0`). The correct entire function whose strip-zeros coincide
(with multiplicity) with the nontrivial zeta zeros is

  `ξ(s) = s·(s-1)·Λ(s) = s·(s-1)·Λ₀(s) + 1`,

using `Λ(s) = Λ₀(s) - 1/s - 1/(1-s)` and the algebraic identity
`s(s-1)·(1/s + 1/(1-s)) = (s-1) - s = -1`.

This file builds `ξ`: entire, finite-order envelope, and a concrete nonzero point
`ξ(2) = π/3 ≠ 0`. (Jensen count + multiplicity bridge follow.)
-/

namespace RHFormalization
open Complex Real MeasureTheory Set MeromorphicOn Metric

/-- The entire xi-type function `ξ(s) = s(s-1)Λ₀(s) + 1`. -/
noncomputable def xiFun (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

/-- `ξ` is entire. -/
theorem xiFun_differentiable : Differentiable ℂ xiFun := by
  unfold xiFun
  apply Differentiable.add
  · exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
      differentiable_completedZeta₀)
  · exact differentiable_const _

theorem xiFun_analyticOnNhd : AnalyticOnNhd ℂ xiFun Set.univ :=
  xiFun_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- **Order bound for `ξ`.** `‖ξ z‖ ≤ exp(C(1+‖z‖)²)` for some `C ≥ 0`. -/
theorem xiFun_order_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖xiFun z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
  obtain ⟨K0, hK00, hbd⟩ := completedZeta0_order_bound
  -- C = K0 + 3 absorbs the polynomial factor ‖z(z-1)‖ ≤ (1+‖z‖)^2 and the +1
  refine ⟨K0 + 3, by linarith, ?_⟩
  intro z
  have hpoly : ‖z * (z - 1)‖ ≤ (1 + ‖z‖) ^ 2 := by
    rw [norm_mul]
    have h1 : ‖z - 1‖ ≤ ‖z‖ + 1 := by
      calc ‖z - 1‖ ≤ ‖z‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = ‖z‖ + 1 := by simp
    calc ‖z‖ * ‖z - 1‖ ≤ ‖z‖ * (‖z‖ + 1) := by
          apply mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  -- ‖ξ z‖ ≤ ‖z(z-1)‖ * ‖Λ₀ z‖ + 1
  have hxi : ‖xiFun z‖ ≤ ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ + 1 := by
    unfold xiFun
    calc ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖
        ≤ ‖z * (z - 1) * completedRiemannZeta₀ z‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ = ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ + 1 := by rw [norm_mul]; simp
  -- combine: ≤ (1+‖z‖)^2 * exp(K0(1+‖z‖)^2) + 1 ≤ exp((K0+3)(1+‖z‖)^2)
  refine le_trans hxi ?_
  set t : ℝ := (1 + ‖z‖) ^ 2 with ht
  have ht1 : 1 ≤ t := by rw [ht]; nlinarith [norm_nonneg z]
  have htpos : 0 ≤ t := by linarith
  have hΛ : ‖completedRiemannZeta₀ z‖ ≤ Real.exp (K0 * t) := hbd z
  -- ‖z(z-1)‖ * ‖Λ₀‖ ≤ t * exp(K0 t)
  have hstep1 : ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ ≤ t * Real.exp (K0 * t) :=
    mul_le_mul hpoly hΛ (norm_nonneg _) htpos
  -- t ≤ exp(t) ≤ exp(t) ; and t * exp(K0 t) + 1 ≤ exp((K0+3)t)
  have ht_le : t ≤ Real.exp t := by
    have := Real.add_one_le_exp t; linarith
  have hcombine : t * Real.exp (K0 * t) + 1 ≤ Real.exp ((K0 + 3) * t) := by
    have hexp1 : t * Real.exp (K0 * t) ≤ Real.exp t * Real.exp (K0 * t) :=
      mul_le_mul_of_nonneg_right ht_le (le_of_lt (Real.exp_pos _))
    have hmerge : Real.exp t * Real.exp (K0 * t) = Real.exp ((K0 + 1) * t) := by
      rw [← Real.exp_add]; ring_nf
    have h1le : (1:ℝ) ≤ Real.exp ((K0 + 1) * t) := by
      rw [Real.one_le_exp_iff]; nlinarith [hK00, htpos]
    have hfinal : Real.exp ((K0 + 1) * t) + 1 ≤ Real.exp ((K0 + 3) * t) := by
      have hgap : Real.exp ((K0 + 1) * t) + Real.exp ((K0 + 1) * t)
          ≤ Real.exp ((K0 + 3) * t) := by
        have : 2 * Real.exp ((K0 + 1) * t) ≤ Real.exp ((K0 + 3) * t) := by
          have h2 : (2:ℝ) ≤ Real.exp (2 * t) := by
            have := Real.add_one_le_exp (2 * t); nlinarith [ht1]
          calc 2 * Real.exp ((K0 + 1) * t)
              ≤ Real.exp (2 * t) * Real.exp ((K0 + 1) * t) :=
                mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos _))
            _ = Real.exp ((K0 + 3) * t) := by rw [← Real.exp_add]; ring_nf
        linarith
      linarith [h1le, hgap]
    calc t * Real.exp (K0 * t) + 1
        ≤ Real.exp t * Real.exp (K0 * t) + 1 := by linarith
      _ = Real.exp ((K0 + 1) * t) + 1 := by rw [hmerge]
      _ ≤ Real.exp ((K0 + 3) * t) := hfinal
  linarith [hstep1, hcombine]

#print axioms xiFun_order_bound

/-- **Sharp order bound for `ξ`.** `‖ξ z‖ ≤ exp(C·(1+‖z‖)(log(2+‖z‖)+1))` — the `O(R log R)`
(Riemann–von Mangoldt rate) envelope. -/
theorem xiFun_order_bound_sharp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖xiFun z‖ ≤ Real.exp (C * ((1 + ‖z‖) * (Real.log (2 + ‖z‖) + 1))) := by
  obtain ⟨K0, hK00, hbd⟩ := completedZeta0_order_bound_sharp
  refine ⟨K0 + 3, by linarith, ?_⟩
  intro z
  set nz : ℝ := ‖z‖ with hnz
  have hnz0 : 0 ≤ nz := norm_nonneg z
  set g : ℝ := (1 + nz) * (Real.log (2 + nz) + 1) with hg
  have hlog2nz_nonneg : 0 ≤ Real.log (2 + nz) := Real.log_nonneg (by linarith)
  have h1nz : (1:ℝ) ≤ 1 + nz := by linarith
  have hg_ge_1nz : (1 + nz) ≤ g := by rw [hg]; nlinarith [hlog2nz_nonneg, h1nz]
  have hg_ge1 : (1:ℝ) ≤ g := le_trans h1nz hg_ge_1nz
  have hgpos : 0 ≤ g := by linarith
  -- polynomial factor
  have hpoly : ‖z * (z - 1)‖ ≤ (1 + nz) ^ 2 := by
    rw [norm_mul]
    have h1 : ‖z - 1‖ ≤ nz + 1 := by
      calc ‖z - 1‖ ≤ ‖z‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = nz + 1 := by rw [hnz]; simp
    calc ‖z‖ * ‖z - 1‖ ≤ nz * (nz + 1) := by
          rw [← hnz]; apply mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ (1 + nz) ^ 2 := by nlinarith [hnz0]
  have hxi : ‖xiFun z‖ ≤ ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ + 1 := by
    unfold xiFun
    calc ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖
        ≤ ‖z * (z - 1) * completedRiemannZeta₀ z‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ = ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ + 1 := by rw [norm_mul]; simp
  refine le_trans hxi ?_
  -- Λ₀ bound in terms of g
  have hΛ : ‖completedRiemannZeta₀ z‖ ≤ Real.exp (K0 * g) := by rw [hg, hnz]; exact hbd z
  -- key: (1+nz)^2 ≤ exp(g).  Via (1+nz)^2 ≤ exp(1+nz) ≤ exp(g).
  have hsq_le_exp : (1 + nz) ^ 2 ≤ Real.exp g := by
    -- (1+nz)^2 ≤ exp(1+nz): use 1+u+u²/2 ≤ exp(u) is overkill; use (1+nz)^2 ≤ exp(2 log(1+nz)) trivially = (1+nz)^2, need ≤ exp(g)
    -- Simn: (1+nz)^2 = exp(2 * log(1+nz)) and 2 log(1+nz) ≤ 1+nz ≤ g
    have hpos1 : (0:ℝ) < 1 + nz := by linarith
    have hpos2 : (0:ℝ) < (1 + nz) ^ 2 := by positivity
    have hrw : (1 + nz) ^ 2 = Real.exp (Real.log ((1 + nz) ^ 2)) := (Real.exp_log hpos2).symm
    rw [hrw, Real.log_pow]
    apply Real.exp_le_exp.mpr
    push_cast
    -- 2 log(1+nz) ≤ 1+nz ≤ g.  Use 2 log u ≤ u via u = (√u)², log u = 2 log √u ≤ 2(√u - 1).
    have hlog_le : (2:ℝ) * Real.log (1 + nz) ≤ 1 + nz := by
      set u : ℝ := 1 + nz with hu
      have husqrt_pos : (0:ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hpos1
      have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt (le_of_lt hpos1)
      have hlogsqrt : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
        Real.log_le_sub_one_of_pos husqrt_pos
      -- log u = 2 log √u
      have hlogu : Real.log u = 2 * Real.log (Real.sqrt u) := by
        rw [Real.log_sqrt (le_of_lt hpos1)]; ring
      rw [hlogu]
      -- 4 log √u ≤ 4(√u - 1) ≤ u  since (√u - 2)² ≥ 0
      nlinarith [hlogsqrt, sq_nonneg (Real.sqrt u - 2), hsq]
    linarith [hlog_le, hg_ge_1nz]
  -- ‖z(z-1)‖ * ‖Λ₀‖ ≤ exp(g) * exp(K0 g) = exp((K0+1)g)
  have hstep1 : ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ ≤ Real.exp g * Real.exp (K0 * g) := by
    apply mul_le_mul (le_trans hpoly hsq_le_exp) hΛ (norm_nonneg _) (Real.exp_nonneg _)
  have hmerge : Real.exp g * Real.exp (K0 * g) = Real.exp ((K0 + 1) * g) := by
    rw [← Real.exp_add]; ring_nf
  -- exp((K0+1)g) + 1 ≤ exp((K0+3)g)
  have h1le : (1:ℝ) ≤ Real.exp ((K0 + 1) * g) := by
    rw [Real.one_le_exp_iff]; nlinarith [hK00, hgpos]
  have hfinal : Real.exp ((K0 + 1) * g) + 1 ≤ Real.exp ((K0 + 3) * g) := by
    have hgap : 2 * Real.exp ((K0 + 1) * g) ≤ Real.exp ((K0 + 3) * g) := by
      have h2 : (2:ℝ) ≤ Real.exp (2 * g) := by
        have := Real.add_one_le_exp (2 * g); nlinarith [hg_ge1]
      calc 2 * Real.exp ((K0 + 1) * g)
          ≤ Real.exp (2 * g) * Real.exp ((K0 + 1) * g) :=
            mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos _))
        _ = Real.exp ((K0 + 3) * g) := by rw [← Real.exp_add]; ring_nf
    linarith [h1le, hgap]
  calc ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ + 1
      ≤ Real.exp ((K0 + 1) * g) + 1 := by rw [← hmerge]; linarith [hstep1]
    _ ≤ Real.exp ((K0 + 3) * g) := hfinal

#print axioms xiFun_order_bound_sharp


/-- `ξ(2) = π/3 ≠ 0`. Concrete nonzero point (Jensen center). Since `Λ₀(2) = (π-3)/6`,
`ξ(2) = 2·1·(π-3)/6 + 1 = (π-3)/3 + 1 = π/3`. -/
theorem xiFun_ne_zero_at_two : xiFun 2 ≠ 0 := by
  have hΛ : completedRiemannZeta₀ 2 = ((π : ℂ) - 3) / 6 := by
    -- reuse the value computed inside completedZeta0_ne_zero_at_two's proof:
    -- we re-derive it here cheaply via the same hLam0 chain is long; instead
    -- extract from the ne_zero lemma is not possible, so recompute the value.
    have he1 : (-2 / 2 : ℂ) = -1 := by norm_num
    have he2 : (2 / 2 : ℂ) = 1 := by norm_num
    have hGammaR2 : Complex.Gammaℝ 2 = (π : ℂ)⁻¹ := by
      rw [Complex.Gammaℝ_def, he1, he2, Complex.cpow_neg_one, Complex.Gamma_one, mul_one]
    have hGammaR2_ne : Complex.Gammaℝ 2 ≠ 0 := by
      rw [hGammaR2]; simp [Real.pi_ne_zero]
    have hLam2 : completedRiemannZeta 2 = (π : ℂ) / 6 := by
      have hdef := riemannZeta_def_of_ne_zero (s := 2) (by norm_num)
      have hLam : completedRiemannZeta 2 = riemannZeta 2 * Complex.Gammaℝ 2 := by
        rw [hdef, div_mul_cancel₀ _ hGammaR2_ne]
      rw [hLam, riemannZeta_two, hGammaR2]
      have hpne : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      field_simp
    have heq := completedRiemannZeta_eq 2
    have hstep : completedRiemannZeta₀ 2 = completedRiemannZeta 2 - 1/2 := by
      rw [heq]; ring_nf
    rw [hstep, hLam2]; ring
  -- ξ(2) = 2*(2-1)*Λ₀(2) + 1 = π/3
  have hval : xiFun 2 = (π : ℂ) / 3 := by
    unfold xiFun
    rw [hΛ]; ring
  rw [hval]
  intro hc
  rw [div_eq_zero_iff] at hc
  rcases hc with h | h
  · have hr : (π : ℝ) = 0 := by exact_mod_cast h
    linarith [Real.pi_gt_three]
  · norm_num at h

#print axioms xiFun_ne_zero_at_two

/-- **Jensen disk-count bound for `ξ`.** Total zero multiplicity of `ξ` in `closedBall 2 |R|`
is `≤ C·(3 + 2R)² + D`. Same Jensen application as for `Λ₀`, now with the correct function. -/
theorem xiFun_disk_count_le :
    ∃ (C D : ℝ), 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ᶠ u, divisor xiFun (closedBall (2:ℂ) |R|) u
        ≤ C * (3 + 2 * R) ^ 2 + D := by
  obtain ⟨K0, hK00, hbound⟩ := xiFun_order_bound
  refine ⟨K0 / Real.log 2, (- Real.log ‖xiFun 2‖) / Real.log 2, ?_, ?_⟩
  · positivity
  intro R hR
  have hRpos : 0 < R := by linarith
  have hr_pos : 0 < |R| := by rw [abs_of_pos hRpos]; exact hRpos
  have hr_lt_R : |R| < |2 * R| := by
    rw [abs_of_pos hRpos, abs_of_pos (by linarith : (0:ℝ) < 2 * R)]; linarith
  set M : ℝ := Real.exp (K0 * (3 + 2 * R) ^ 2) with hM
  have hM1 : 1 ≤ M := by rw [hM, Real.one_le_exp_iff]; positivity
  have h₁f : AnalyticOnNhd ℂ xiFun (closedBall (2:ℂ) |2 * R|) :=
    xiFun_analyticOnNhd.mono (Set.subset_univ _)
  have h₂f : xiFun 2 ≠ 0 := xiFun_ne_zero_at_two
  have f_bound : ∀ z ∈ sphere (2:ℂ) |2 * R|, ‖xiFun z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hznorm : ‖z‖ ≤ 2 + 2 * R := by
      have h1 : ‖z‖ ≤ ‖(2:ℂ)‖ + ‖z - 2‖ := by
        calc ‖z‖ = ‖(2:ℂ) + (z - 2)‖ := by ring_nf
          _ ≤ ‖(2:ℂ)‖ + ‖z - 2‖ := norm_add_le _ _
      rw [hz, abs_of_pos (by linarith : (0:ℝ) < 2 * R)] at h1
      have h2 : ‖(2:ℂ)‖ = 2 := by simp
      rw [h2] at h1; linarith
    refine le_trans (hbound z) ?_
    rw [hM]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hK00
    have : (1 + ‖z‖) ≤ (3 + 2 * R) := by linarith
    nlinarith [norm_nonneg z, this, hR]
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := 2) (r := R) (R := 2 * R) (M := M)
    hr_pos hr_lt_R hM1 h₁f h₂f f_bound
  refine le_trans hjensen ?_
  have hlog2R : Real.log (2 * R / R) = Real.log 2 := by
    rw [mul_div_assoc, div_self (ne_of_gt hRpos), mul_one]
  rw [hlog2R]
  have hnorm_pos : 0 < ‖xiFun 2‖ := by rw [norm_pos_iff]; exact h₂f
  have hMpos : 0 < M := Real.exp_pos _
  have hlogM : Real.log (M / ‖xiFun 2‖)
      = K0 * (3 + 2 * R) ^ 2 - Real.log ‖xiFun 2‖ := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hnorm_pos), hM, Real.log_exp]
  rw [hlogM]
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  apply le_of_eq
  field_simp
  ring

#print axioms xiFun_disk_count_le

/-- **Sharp Jensen disk-count for `ξ`** — `O(R log R)` rate.
`∑ divisor ξ (closedBall 2 |R|) ≤ C·(3+2R)(log(4+2R)+1) + D`. -/
theorem xiFun_disk_count_le_sharp :
    ∃ (C D : ℝ), 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ᶠ u, divisor xiFun (closedBall (2:ℂ) |R|) u
        ≤ C * ((3 + 2 * R) * (Real.log (4 + 2 * R) + 1)) + D := by
  obtain ⟨K0, hK00, hbound⟩ := xiFun_order_bound_sharp
  refine ⟨K0 / Real.log 2, (- Real.log ‖xiFun 2‖) / Real.log 2, ?_, ?_⟩
  · positivity
  intro R hR
  have hRpos : 0 < R := by linarith
  have hr_pos : 0 < |R| := by rw [abs_of_pos hRpos]; exact hRpos
  have hr_lt_R : |R| < |2 * R| := by
    rw [abs_of_pos hRpos, abs_of_pos (by linarith : (0:ℝ) < 2 * R)]; linarith
  set G : ℝ := (3 + 2 * R) * (Real.log (4 + 2 * R) + 1) with hG
  set M : ℝ := Real.exp (K0 * G) with hM
  have hM1 : 1 ≤ M := by
    rw [hM, Real.one_le_exp_iff, hG]
    have hl : 0 ≤ Real.log (4 + 2 * R) := Real.log_nonneg (by linarith)
    positivity
  have h₁f : AnalyticOnNhd ℂ xiFun (closedBall (2:ℂ) |2 * R|) :=
    xiFun_analyticOnNhd.mono (Set.subset_univ _)
  have h₂f : xiFun 2 ≠ 0 := xiFun_ne_zero_at_two
  have f_bound : ∀ z ∈ sphere (2:ℂ) |2 * R|, ‖xiFun z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hznorm : ‖z‖ ≤ 2 + 2 * R := by
      have h1 : ‖z‖ ≤ ‖(2:ℂ)‖ + ‖z - 2‖ := by
        calc ‖z‖ = ‖(2:ℂ) + (z - 2)‖ := by ring_nf
          _ ≤ ‖(2:ℂ)‖ + ‖z - 2‖ := norm_add_le _ _
      rw [hz, abs_of_pos (by linarith : (0:ℝ) < 2 * R)] at h1
      have h2 : ‖(2:ℂ)‖ = 2 := by simp
      rw [h2] at h1; linarith
    refine le_trans (hbound z) ?_
    rw [hM]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hK00
    rw [hG]
    -- (1+‖z‖)(log(2+‖z‖)+1) ≤ (3+2R)(log(4+2R)+1)
    have hzn0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hfac1 : (1 + ‖z‖) ≤ (3 + 2 * R) := by linarith
    have hfac2 : Real.log (2 + ‖z‖) + 1 ≤ Real.log (4 + 2 * R) + 1 := by
      have hmono : Real.log (2 + ‖z‖) ≤ Real.log (4 + 2 * R) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hp1 : 0 ≤ Real.log (2 + ‖z‖) + 1 := by
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 + ‖z‖); linarith
    have hp2 : 0 ≤ (3 + 2 * R) := by linarith
    calc (1 + ‖z‖) * (Real.log (2 + ‖z‖) + 1)
        ≤ (3 + 2 * R) * (Real.log (2 + ‖z‖) + 1) :=
          mul_le_mul_of_nonneg_right hfac1 hp1
      _ ≤ (3 + 2 * R) * (Real.log (4 + 2 * R) + 1) :=
          mul_le_mul_of_nonneg_left hfac2 hp2
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := 2) (r := R) (R := 2 * R) (M := M)
    hr_pos hr_lt_R hM1 h₁f h₂f f_bound
  refine le_trans hjensen ?_
  have hlog2R : Real.log (2 * R / R) = Real.log 2 := by
    rw [mul_div_assoc, div_self (ne_of_gt hRpos), mul_one]
  rw [hlog2R]
  have hnorm_pos : 0 < ‖xiFun 2‖ := by rw [norm_pos_iff]; exact h₂f
  have hMpos : 0 < M := Real.exp_pos _
  have hlogM : Real.log (M / ‖xiFun 2‖) = K0 * G - Real.log ‖xiFun 2‖ := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hnorm_pos), hM, Real.log_exp]
  rw [hlogM]
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  apply le_of_eq
  rw [hG]
  field_simp
  ring

#print axioms xiFun_disk_count_le_sharp


/-- Pointwise identity: `ξ(s) = s(s-1)·Gammaℝ(s)·ζ(s)` for `s ≠ 0, 1` with `0 < re s`
(so `Gammaℝ s ≠ 0`). -/
theorem xiFun_eq_mul_zeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsre : 0 < s.re) :
    xiFun s = (s * (s - 1) * Complex.Gammaℝ s) * riemannZeta s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero_of_ne (Ne.symm hs1)
  have hGne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
  -- ξ s = s(s-1) * Λ s
  have hxi_eq_Λ : xiFun s = s * (s - 1) * completedRiemannZeta s := by
    unfold xiFun
    rw [completedRiemannZeta_eq s]
    field_simp
    ring
  rw [hxi_eq_Λ]
  -- Λ s = Gammaℝ s * ζ s, from ζ s = Λ s / Gammaℝ s
  have hΛζ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hGne]
  rw [hΛζ]; ring

#print axioms xiFun_eq_mul_zeta

/-- The strip open set `{s | 0 < re s ∧ re s < 1}` — contains all nontrivial zeros, avoids 0,1. -/
private def stripSet : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

private theorem isOpen_stripSet : IsOpen stripSet := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt Complex.continuous_re continuous_const

/-- **Multiplicity bridge.** For a nontrivial zeta zero `ρ`, the analytic order of `ξ` at `ρ`
equals the analytic order of `ζ` at `ρ`. (Because `ξ = (s(s-1)Gammaℝ)·ζ` and the bracket is
analytic & nonzero in the strip, contributing order 0.) -/
theorem xiFun_order_eq_zeta_order {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    analyticOrderAt xiFun ρ = analyticOrderAt riemannZeta ρ := by
  obtain ⟨hz, h0, h1⟩ := hρ
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  -- ginv = (s(s-1)Gammaℝ)⁻¹, analytic on stripSet (open, contains ρ)
  set ginv : ℂ → ℂ := fun s => (s * (s - 1) * Complex.Gammaℝ s)⁻¹ with hginv
  have hρmem : ρ ∈ stripSet := ⟨h0, h1⟩
  have hginv_analytic : AnalyticOnNhd ℂ ginv stripSet := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_stripSet
    intro s hs
    obtain ⟨hs0re, hs1re⟩ := hs
    have hsne0 : s ≠ 0 := by intro h; rw [h] at hs0re; simp at hs0re
    have hsne1 : s ≠ 1 := by intro h; rw [h] at hs1re; simp at hs1re
    have hGℝinv : DifferentiableAt ℂ (fun s => (Complex.Gammaℝ s)⁻¹) s :=
      Complex.differentiable_Gammaℝ_inv s
    -- ginv s = (s(s-1))⁻¹ * (Gammaℝ s)⁻¹
    have hpoly_inv : DifferentiableAt ℂ (fun s => (s * (s - 1))⁻¹) s := by
      apply DifferentiableAt.inv
      · exact (differentiableAt_id.mul (differentiableAt_id.sub_const 1))
      · exact mul_ne_zero hsne0 (sub_ne_zero_of_ne hsne1)
    have hprod : DifferentiableAt ℂ (fun s => (s * (s - 1))⁻¹ * (Complex.Gammaℝ s)⁻¹) s :=
      hpoly_inv.mul hGℝinv
    have heqfun : (fun s => (s * (s - 1))⁻¹ * (Complex.Gammaℝ s)⁻¹) = ginv := by
      rw [hginv]; funext y; rw [← mul_inv]
    rw [heqfun] at hprod
    exact hprod.differentiableWithinAt
  -- ζ =ᶠ[𝓝 ρ] ξ * ginv
  have hEq : riemannZeta =ᶠ[nhds ρ] (fun s => xiFun s * ginv s) := by
    have hUnhds : stripSet ∈ nhds ρ := isOpen_stripSet.mem_nhds hρmem
    filter_upwards [hUnhds] with s hs
    obtain ⟨hs0re, hs1re⟩ := hs
    have hsne0 : s ≠ 0 := by intro h; rw [h] at hs0re; simp at hs0re
    have hsne1 : s ≠ 1 := by intro h; rw [h] at hs1re; simp at hs1re
    have hGne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0re
    have hbracket : s * (s - 1) * Complex.Gammaℝ s ≠ 0 :=
      mul_ne_zero (mul_ne_zero hsne0 (sub_ne_zero_of_ne hsne1)) hGne
    simp only [hginv]
    rw [xiFun_eq_mul_zeta hsne0 hsne1 hs0re]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero_of_ne hsne1
    field_simp
  -- order(ζ) = order(ξ * ginv) = order(ξ) + order(ginv) = order(ξ) + 0
  rw [analyticOrderAt_congr hEq]
  have hξA : AnalyticAt ℂ xiFun ρ := xiFun_analyticOnNhd ρ (Set.mem_univ _)
  have hginvA : AnalyticAt ℂ ginv ρ := hginv_analytic ρ hρmem
  have hmul_eq : (fun s => xiFun s * ginv s) = xiFun * ginv := rfl
  rw [hmul_eq, analyticOrderAt_mul hξA hginvA]
  have hginv_ne : ginv ρ ≠ 0 := by
    rw [hginv]
    apply inv_ne_zero
    have hGne : Complex.Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
    exact mul_ne_zero (mul_ne_zero hρ0 (sub_ne_zero_of_ne hρ1)) hGne
  rw [hginvA.analyticOrderAt_eq_zero.mpr hginv_ne, add_zero]

#print axioms xiFun_order_eq_zeta_order

/-- For a nontrivial zeta zero `ρ` in `closedBall 2 |R|`, the `ξ`-divisor equals the zeta
multiplicity: `divisor ξ (closedBall 2 |R|) ρ = (zetaZeroMult ρ : ℤ)`. -/
theorem xiFun_divisor_eq_mult {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) {R : ℝ}
    (hmem : ρ ∈ Metric.closedBall (2:ℂ) |R|) :
    divisor xiFun (Metric.closedBall (2:ℂ) |R|) ρ = (zetaZeroMult ρ : ℤ) := by
  obtain ⟨hz, h0, h1⟩ := hρ
  -- ζ analytic at ρ, order finite and equal to zetaZeroMult
  have hζA : AnalyticAt ℂ riemannZeta ρ := zeta_analyticOnNhd_re_lt_one ρ h1
  have hne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro h
    exact zeta_not_locally_zero ρ h1 (analyticOrderAt_eq_top.mp h)
  -- analyticOrderAt ζ ρ = (zetaZeroMult ρ : ℕ∞)
  have hord_zeta : analyticOrderAt riemannZeta ρ = (zetaZeroMult ρ : ℕ∞) := by
    unfold zetaZeroMult
    rw [ENat.coe_toNat hne_top]
  -- ξ analytic on the ball
  have h₁f : AnalyticOnNhd ℂ xiFun (Metric.closedBall (2:ℂ) |R|) :=
    xiFun_analyticOnNhd.mono (Set.subset_univ _)
  -- divisor ξ = order ξ (mapped) = order ζ (mapped) = mult
  rw [h₁f.divisor_apply hmem, xiFun_order_eq_zeta_order ⟨hz, h0, h1⟩, hord_zeta]
  simp

#print axioms xiFun_divisor_eq_mult

/-- Geometry: every nontrivial zeta zero in band `k` lies in `closedBall 2 (k+4)`.
(`re ∈ [0,1]` so `|re-2| ≤ 2`; `|im| ≤ k+1`; hence `‖ρ-2‖ ≤ |re-2|+|im| ≤ k+3 ≤ k+4`.) -/
theorem band_mem_ball {ρ : ℂ} {k : ℕ}
    (hρ : IsNontrivialZetaZero ρ ∧ ⌊|ρ.im|⌋₊ = k) :
    ρ ∈ Metric.closedBall (2:ℂ) |(k:ℝ) + 4| := by
  obtain ⟨⟨hz, h0, h1⟩, hband⟩ := hρ
  rw [Metric.mem_closedBall, Complex.dist_eq]
  have him : |ρ.im| ≤ (k : ℝ) + 1 := by
    have := Nat.lt_floor_add_one |ρ.im|
    rw [hband] at this; linarith
  -- ‖ρ - 2‖ ≤ |（ρ-2).re| + |(ρ-2).im| = |ρ.re - 2| + |ρ.im|
  have hnorm : ‖ρ - 2‖ ≤ |(ρ - 2).re| + |(ρ - 2).im| := by
    have := Complex.norm_le_abs_re_add_abs_im (ρ - 2)
    exact this
  have hre : |(ρ - 2).re| ≤ 2 := by
    rw [Complex.sub_re, Complex.re_ofNat]
    rw [abs_le]; constructor <;> linarith
  have himre : |(ρ - 2).im| = |ρ.im| := by
    rw [Complex.sub_im, Complex.im_ofNat]; simp
  have hk4 : (0:ℝ) ≤ (k:ℝ) + 4 := by positivity
  rw [abs_of_nonneg hk4]
  calc ‖ρ - 2‖ ≤ |(ρ - 2).re| + |(ρ - 2).im| := hnorm
    _ = |(ρ - 2).re| + |ρ.im| := by rw [himre]
    _ ≤ 2 + ((k:ℝ) + 1) := by linarith [hre, him]
    _ ≤ (k:ℝ) + 4 := by linarith

#print axioms band_mem_ball

/-- **Band ≤ disk count.** `bandTotal k ≤ (ξ-divisor finsum over closedBall 2 (k+4) : ℝ)`. -/
theorem bandTotal_le_xiCount (k : ℕ) :
    bandTotal k ≤ ((∑ᶠ u, divisor xiFun (Metric.closedBall (2:ℂ) |(k:ℝ) + 4|) u : ℤ) : ℝ) := by
  set R : ℝ := |(k:ℝ) + 4| with hR
  set D := divisor xiFun (Metric.closedBall (2:ℂ) R) with hD
  have hDnn : ∀ u, 0 ≤ D u := fun u =>
    xiFun_analyticOnNhd.mono (Set.subset_univ _) |>.divisor_nonneg u
  -- finite support of D
  have hDsupp : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall 2 R)
  -- the integer band sum
  set bandFin := (band_finite k).toFinset with hbandFin
  set S : Finset ℂ := hDsupp.toFinset ∪ bandFin with hS
  -- ∑ᶠ D = ∑_{S} D  (support ⊆ S)
  have hfinsum : (∑ᶠ u, D u) = ∑ u ∈ S, D u := by
    apply finsum_eq_finsetSum_of_support_subset
    intro u hu
    rw [hS, Finset.coe_union, Set.Finite.coe_toFinset]
    left; exact hu
  -- ∑_{band} (mult) = ∑_{band} D  (xiFun_divisor_eq_mult)
  have hbandsum : ∑ ρ ∈ bandFin, (zetaZeroMult ρ : ℤ) = ∑ ρ ∈ bandFin, D ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hbandFin, Set.Finite.mem_toFinset] at hρ
    have hmem : ρ ∈ Metric.closedBall (2:ℂ) R := by rw [hR]; exact band_mem_ball hρ
    obtain ⟨hnt, _⟩ := hρ
    rw [hD, hR]; exact (xiFun_divisor_eq_mult hnt (by rw [← hR]; exact hmem)).symm
  -- ∑_{band} D ≤ ∑_{S} D  (band ⊆ S, D nonneg)
  have hsub : bandFin ⊆ S := by rw [hS]; exact Finset.subset_union_right
  have hdom : ∑ ρ ∈ bandFin, D ρ ≤ ∑ u ∈ S, D u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hDnn i)
  -- chain in ℤ: ∑_{band} mult ≤ ∑ᶠ D
  have hZ : ∑ ρ ∈ bandFin, (zetaZeroMult ρ : ℤ) ≤ ∑ᶠ u, D u := by
    rw [hfinsum, hbandsum]; exact hdom
  -- bandTotal = (∑_{band} mult : ℝ)
  have hbtR : bandTotal k = ((∑ ρ ∈ bandFin, (zetaZeroMult ρ : ℤ) : ℤ) : ℝ) := by
    rw [bandTotal, hbandFin]
    push_cast
    apply Finset.sum_congr rfl
    intro ρ _
    show (defaultZeroMultiplicityData.mult ρ : ℝ) = ((zetaZeroMult ρ : ℤ) : ℝ)
    rw [show defaultZeroMultiplicityData.mult ρ = zetaZeroMult ρ from rfl]
    push_cast; ring
  rw [hbtR]
  exact_mod_cast hZ

#print axioms bandTotal_le_xiCount

/-- **Combined: `bandTotal k = O(k²)`.** There exist `C ≥ 0, D` with
`bandTotal k ≤ C·(3 + 2(k+4))² + D` for all `k`. -/
theorem bandTotal_quadratic_bound :
    ∃ (C D : ℝ), 0 ≤ C ∧ ∀ k : ℕ, bandTotal k ≤ C * (3 + 2 * ((k:ℝ) + 4)) ^ 2 + D := by
  obtain ⟨C, Dconst, hC0, hbound⟩ := xiFun_disk_count_le
  refine ⟨C, Dconst, hC0, ?_⟩
  intro k
  have hk1 : (1:ℝ) ≤ (k:ℝ) + 4 := by have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith
  have hcount := hbound ((k:ℝ) + 4) hk1
  -- bandTotal k ≤ (finsum : ℝ) ≤ (RHS : ℝ)
  refine le_trans (bandTotal_le_xiCount k) ?_
  -- need: (finsum over closedBall 2 |k+4| : ℝ) ≤ C(3+2(k+4))² + D
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 4)] at hcount ⊢
  exact_mod_cast hcount

#print axioms bandTotal_quadratic_bound

/-- **Sharp `bandTotal k = O(k log k)`.** There exist `C ≥ 0, D` with
`bandTotal k ≤ C·(3+2(k+4))(log(4+2(k+4))+1) + D` for all `k`. -/
theorem bandTotal_loglinear_bound :
    ∃ (C D : ℝ), 0 ≤ C ∧ ∀ k : ℕ,
      bandTotal k ≤ C * ((3 + 2 * ((k:ℝ) + 4)) * (Real.log (4 + 2 * ((k:ℝ) + 4)) + 1)) + D := by
  obtain ⟨C, Dconst, hC0, hbound⟩ := xiFun_disk_count_le_sharp
  refine ⟨C, Dconst, hC0, ?_⟩
  intro k
  have hk1 : (1:ℝ) ≤ (k:ℝ) + 4 := by
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith
  have hcount := hbound ((k:ℝ) + 4) hk1
  refine le_trans (bandTotal_le_xiCount k) ?_
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 4)] at hcount ⊢
  exact_mod_cast hcount

#print axioms bandTotal_loglinear_bound

/-- Bands have pairwise-disjoint underlying Finsets (distinct floor-of-`|im|` values). -/
theorem band_disjoint {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (band_finite j).toFinset (band_finite k).toFinset := by
  rw [Finset.disjoint_left]
  intro ρ hj hk
  rw [Set.Finite.mem_toFinset] at hj hk
  obtain ⟨_, hjeq⟩ := hj
  obtain ⟨_, hkeq⟩ := hk
  exact hjk (by rw [← hjeq, ← hkeq])

/-- **Cumulative band ≤ single-disk count.** `∑_{k≤n} bandTotal k ≤ ∑ᶠ divisor ξ (disk 2 (n+5))`.
This is the TIGHT cumulative bound (all bands up to `n` fit in one disk), giving `N(n)=O(n log n)`
rather than the lossy `O(n² log n)` from summing per-band bounds. -/
theorem cumulativeBand_le_xiCount (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), bandTotal k
      ≤ ((∑ᶠ u, divisor xiFun (Metric.closedBall (2:ℂ) |(n:ℝ) + 5|) u : ℤ) : ℝ) := by
  set R : ℝ := |(n:ℝ) + 5| with hR
  set D := divisor xiFun (Metric.closedBall (2:ℂ) R) with hD
  have hDnn : ∀ u, 0 ≤ D u := fun u =>
    xiFun_analyticOnNhd.mono (Set.subset_univ _) |>.divisor_nonneg u
  have hDsupp : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall 2 R)
  -- combined finset: biUnion of bands 0..n
  set U : Finset ℂ := (Finset.range (n + 1)).biUnion (fun k => (band_finite k).toFinset) with hU
  -- pairwise disjoint
  have hdisj : (Finset.range (n + 1) : Set ℕ).PairwiseDisjoint
      (fun k => (band_finite k).toFinset) := by
    intro j _ k _ hjk
    exact band_disjoint hjk
  -- ∑_{k≤n} bandTotal k = ∑_{ρ∈U} (mult : ℝ)
  have hsum_eq : ∑ k ∈ Finset.range (n + 1), bandTotal k
      = ∑ ρ ∈ U, (defaultZeroMultiplicityData.mult ρ : ℝ) := by
    rw [hU, Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro k _; rw [bandTotal]
  rw [hsum_eq]
  -- each ρ ∈ U lies in disk(n+5), with mult = D ρ
  set S : Finset ℂ := hDsupp.toFinset ∪ U with hS
  have hfinsum : (∑ᶠ u, D u) = ∑ u ∈ S, D u := by
    apply finsum_eq_finsetSum_of_support_subset
    intro u hu
    rw [hS, Finset.coe_union, Set.Finite.coe_toFinset]
    left; exact hu
  -- ∑_{U} mult = ∑_{U} D
  have hUmem : ∀ ρ ∈ U, ρ ∈ Metric.closedBall (2:ℂ) R := by
    intro ρ hρU
    rw [hU, Finset.mem_biUnion] at hρU
    obtain ⟨k, hkr, hρk⟩ := hρU
    rw [Set.Finite.mem_toFinset] at hρk
    obtain ⟨hnt, hfloor⟩ := hρk
    rw [Finset.mem_range] at hkr
    -- band_mem_ball gives ρ ∈ disk(k+4) ⊆ disk(n+5)
    have hk4 : ρ ∈ Metric.closedBall (2:ℂ) |(k:ℝ) + 4| := band_mem_ball ⟨hnt, hfloor⟩
    rw [Metric.mem_closedBall] at hk4 ⊢
    rw [hR, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 5)]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 4)] at hk4
    have hkn : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.le_of_lt_succ hkr
    linarith
  have hUmult : ∑ ρ ∈ U, (defaultZeroMultiplicityData.mult ρ : ℝ)
      = ((∑ ρ ∈ U, D ρ : ℤ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro ρ hρU
    have hmem : ρ ∈ Metric.closedBall (2:ℂ) R := hUmem ρ hρU
    rw [hU, Finset.mem_biUnion] at hρU
    obtain ⟨k, _, hρk⟩ := hρU
    rw [Set.Finite.mem_toFinset] at hρk
    obtain ⟨hnt, _⟩ := hρk
    show (defaultZeroMultiplicityData.mult ρ : ℝ) = ((D ρ : ℤ) : ℝ)
    rw [show defaultZeroMultiplicityData.mult ρ = zetaZeroMult ρ from rfl, hD]
    rw [xiFun_divisor_eq_mult hnt hmem]
    push_cast; ring
  -- domination: ∑_U D ≤ ∑_S D = ∑ᶠ D  (U ⊆ S, D nonneg)
  rw [hUmult]
  have hsub : U ⊆ S := by rw [hS]; exact Finset.subset_union_right
  have hdom : ∑ ρ ∈ U, D ρ ≤ ∑ u ∈ S, D u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hDnn i)
  have hZ : (∑ ρ ∈ U, D ρ) ≤ ∑ᶠ u, D u := by rw [hfinsum]; exact hdom
  exact_mod_cast hZ

#print axioms cumulativeBand_le_xiCount

/-- **Cumulative count is `O(n log n)`.** `∑_{k≤n} bandTotal k ≤ C·(n+5)(log(2n+...)+1) + D`,
the Riemann–von Mangoldt rate for the partial sums (Jensen single-disk bound). -/
theorem cumulativeBand_loglinear :
    ∃ (C D : ℝ), 0 ≤ C ∧ ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1), bandTotal k
        ≤ C * ((3 + 2 * ((n:ℝ) + 5)) * (Real.log (4 + 2 * ((n:ℝ) + 5)) + 1)) + D := by
  obtain ⟨C, Dconst, hC0, hbound⟩ := xiFun_disk_count_le_sharp
  refine ⟨C, Dconst, hC0, ?_⟩
  intro n
  have hk1 : (1:ℝ) ≤ (n:ℝ) + 5 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
  have hcount := hbound ((n:ℝ) + 5) hk1
  refine le_trans (cumulativeBand_le_xiCount n) ?_
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 5)] at hcount ⊢
  exact_mod_cast hcount

#print axioms cumulativeBand_loglinear





end RHFormalization
