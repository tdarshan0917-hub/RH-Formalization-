#!/bin/zsh
echo "===== 0. name mini-battery ====="
cat > IsoBattery.lean <<'EOF'
import RHFormalization.ReflectionPairPoleClass
open Complex RHFormalization
#check @Complex.abs_re_le_abs
#check @Complex.abs_re_le_norm
#check @Complex.mul_re
#check @Complex.mul_im
#check @isCompact_Icc
#check @IsCompact.prod
example : Continuous polePoint := by
  unfold polePoint
  fun_prop
EOF
lake env lean IsoBattery.lean 2>&1 | head -12
echo "===== 1. install PairPoleIsolation ====="
cat > RHFormalization/PairPoleIsolation.lean <<'EOF'
import RHFormalization.ReflectionPairPoleClass

/-!
# RHFormalization.PairPoleIsolation

The witness pole point is isolated among ALL pole points: there is a radius
r > 0 such that no nontrivial zero outside the reflection pair {ρ, 1−ρ} has
its pole point within r of s0. Key inequality: im(ρ)² ≤ ‖polePoint ρ‖ on the
strip, so offending zeros live in a compact rectangle; an accumulation point a
has polePoint a = s0 by continuity, hence a ∈ {ρ, 1−ρ} by the factorization —
interior strip points where the isolated-zeros dichotomy applies.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric

theorem continuous_polePoint : Continuous polePoint := by
  unfold polePoint
  fun_prop

/-- On the closed strip, im² is controlled by the pole-point norm. -/
theorem im_sq_le_norm_polePoint
    (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    ρ.im ^ 2 ≤ ‖polePoint ρ‖ := by
  have hre : (polePoint ρ).re = -(ρ.re * (1 - ρ.re) + ρ.im ^ 2) := by
    unfold polePoint
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.neg_re]
    ring
  have habs : |(polePoint ρ).re| ≤ ‖polePoint ρ‖ := by
    first
      | exact Complex.abs_re_le_abs _
      | exact Complex.abs_re_le_norm _
      | exact abs_re_le_norm _
  have hnn : 0 ≤ ρ.re * (1 - ρ.re) := by nlinarith
  have : |(polePoint ρ).re| = ρ.re * (1 - ρ.re) + ρ.im ^ 2 := by
    rw [hre, abs_neg, abs_of_nonneg (by positivity)]
  nlinarith [habs, this]

/-- The witness pole point is isolated among pole points of zeros outside the
reflection pair. -/
theorem pairPole_isolated (W : ZeroWitness) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' →
        ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
          r ≤ dist (polePoint ρ') W.s0 := by
  by_contra hcon
  push_neg at hcon
  -- extract an offending sequence at radii 1/(k+1)
  have hseq : ∀ k : ℕ, ∃ ρ' : ℂ,
      IsNontrivialZetaZero ρ' ∧ ρ' ≠ W.ρ ∧ ρ' ≠ 1 - W.ρ ∧
        dist (polePoint ρ') W.s0 < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨ρ', h1, h2, h3, h4⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨ρ', h1, h2, h3, h4⟩
  choose x hx_zero hx_ne1 hx_ne2 hx_dist using hseq
  -- the offenders live in a compact rectangle
  set T : ℝ := Real.sqrt (‖W.s0‖ + 1) with hT
  have hxK : ∀ k : ℕ, x k ∈
      (Set.Icc (0:ℝ) 1 ×ℂ Set.Icc (-T) T) := by
    intro k
    obtain ⟨_, hre0, hre1⟩ := hx_zero k
    have hbound : ‖polePoint (x k)‖ ≤ ‖W.s0‖ + 1 := by
      have hd := hx_dist k
      have h1k : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) k]
      calc ‖polePoint (x k)‖
          ≤ dist (polePoint (x k)) W.s0 + ‖W.s0‖ := by
            rw [dist_eq_norm]
            simpa using norm_sub_norm_le (polePoint (x k)) W.s0 |>.trans (le_abs_self _)
        _ ≤ 1 + ‖W.s0‖ := by linarith [hd.le.trans h1k]
        _ = ‖W.s0‖ + 1 := by ring
    have him : (x k).im ^ 2 ≤ ‖W.s0‖ + 1 :=
      (im_sq_le_norm_polePoint (x k) (le_of_lt hre0) (le_of_lt hre1)).trans hbound
    have hT2 : T ^ 2 = ‖W.s0‖ + 1 := by
      rw [hT, Real.sq_sqrt (by positivity)]
    constructor
    · exact ⟨le_of_lt hre0, le_of_lt hre1⟩
    · constructor
      · nlinarith [him, hT2, Real.sqrt_nonneg (‖W.s0‖ + 1)]
      · nlinarith [him, hT2, Real.sqrt_nonneg (‖W.s0‖ + 1)]
  -- compactness: a convergent subsequence with limit a
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ℂ Set.Icc (-T) T) := by
    first
      | exact (isCompact_Icc.prod isCompact_Icc).reProdIm
      | exact IsCompact.reProdIm isCompact_Icc isCompact_Icc
      | exact isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨a, _haK, φ, hφ, htend⟩ := hcompact.tendsto_subseq hxK
  -- the limit's pole point is s0, so a is in the reflection pair
  have hpp_tend : Tendsto (fun k => polePoint (x (φ k))) atTop (nhds (polePoint a)) :=
    (continuous_polePoint.tendsto a).comp htend
  have hpp_s0 : Tendsto (fun k => polePoint (x (φ k))) atTop (nhds W.s0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => (hx_dist (φ k)).le) ?_
    have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact this.comp (hφ.tendsto_atTop)
  have hpa : polePoint a = W.s0 := tendsto_nhds_unique hpp_tend hpp_s0
  have hfact : a = W.ρ ∨ a = 1 - W.ρ := by
    have heq : W.ρ * (1 - W.ρ) = a * (1 - a) := by
      have h1 : polePoint a = polePoint W.ρ := by rw [hpa, W.hs0_def]
      unfold polePoint at h1
      have := neg_injective h1
      linarith [congrArg Complex.re this]  -- placeholder; replaced below
    exact Or.inl rfl  -- placeholder; replaced below
  sorry

end

end RHFormalization
EOF
echo "DRAFT MODE: probing the two hard steps before committing"
lake env lean RHFormalization/PairPoleIsolation.lean 2>&1 | grep -e "error" -e "sorry" | head -20
rm RHFormalization/PairPoleIsolation.lean
echo "===== probe complete (file removed; this run banks nothing) ====="
