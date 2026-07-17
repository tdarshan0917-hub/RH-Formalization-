import RHFormalization.MeromorphyOffCritical

/-!
# RHFormalization.MeromorphyAwayFromPoles

Meromorphy campaign, installment M2: at every point of Ω off the pole set,
Zpole is AnalyticAt (hence MeromorphicAt). Pole points cannot accumulate at a
non-pole point of Ω: an accumulation point a of zeros would satisfy ζ(a) = 0
(continuity), a ∉ {0,1} (their pole point 0 is outside Ω), re a < 1
(zero-free line re ≥ 1), re a > 0 (functional-equation transfer to re = 1) —
making a a nontrivial zero whose pole point IS x, contradiction.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

/-- Pole points are uniformly separated from any non-pole point of Ω. -/
theorem nonpole_isolated (x : ℂ) (hxΩ : x ∈ Ω) (hx : x ∉ ZeroPoleSet) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ → r ≤ dist (polePoint ρ) x := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ ρ : ℂ,
      IsNontrivialZetaZero ρ ∧ dist (polePoint ρ) x < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨ρ, h1, h2⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨ρ, h1, h2⟩
  choose z hz_zero hz_dist using hseq
  set T : ℝ := Real.sqrt (‖x‖ + 1) with hT
  have hzK : ∀ k : ℕ, z k ∈ (Set.Icc (0:ℝ) 1 ×ℂ Set.Icc (-T) T) := by
    intro k
    obtain ⟨_, hre0, hre1⟩ := hz_zero k
    have hbound : ‖polePoint (z k)‖ ≤ ‖x‖ + 1 := by
      have hd := hz_dist k
      have h1k : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) k]
      calc ‖polePoint (z k)‖
          ≤ dist (polePoint (z k)) x + ‖x‖ := by
            rw [dist_eq_norm]
            simpa using norm_sub_norm_le (polePoint (z k)) x |>.trans (le_abs_self _)
        _ ≤ 1 + ‖x‖ := by linarith [hd.le.trans h1k]
        _ = ‖x‖ + 1 := by ring
    have him : (z k).im ^ 2 ≤ ‖x‖ + 1 :=
      (im_sq_le_norm_polePoint (z k) (le_of_lt hre0) (le_of_lt hre1)).trans hbound
    have hT2 : T ^ 2 = ‖x‖ + 1 := by
      rw [hT, Real.sq_sqrt (by positivity)]
    constructor
    · exact ⟨le_of_lt hre0, le_of_lt hre1⟩
    · constructor
      · nlinarith [him, hT2, Real.sqrt_nonneg (‖x‖ + 1)]
      · nlinarith [him, hT2, Real.sqrt_nonneg (‖x‖ + 1)]
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ℂ Set.Icc (-T) T) := by
    first
      | exact (isCompact_Icc.prod isCompact_Icc).reProdIm
      | exact IsCompact.reProdIm isCompact_Icc isCompact_Icc
      | exact isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨a, haK, φ, hφ, htend⟩ := hcompact.tendsto_subseq hzK
  have hpp_tend : Tendsto (fun k => polePoint (z (φ k))) atTop (nhds (polePoint a)) :=
    (continuous_polePoint.tendsto a).comp htend
  have hpp_x : Tendsto (fun k => polePoint (z (φ k))) atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => (hz_dist (φ k)).le) ?_
    have hbase : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact hbase.comp (hφ.tendsto_atTop)
  have hpa : polePoint a = x := tendsto_nhds_unique hpp_tend hpp_x
  -- a ∉ {0, 1}: their pole point is 0, which lies outside Ω
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hpa
    have : x = 0 := by
      rw [← hpa]; unfold polePoint; ring
    rw [this] at hxΩ
    exact hxΩ ⟨by simp, by simp⟩
  have ha1 : a ≠ 1 := by
    intro h
    rw [h] at hpa
    have : x = 0 := by
      rw [← hpa]; unfold polePoint; ring
    rw [this] at hxΩ
    exact hxΩ ⟨by simp, by simp⟩
  -- ζ(a) = 0 by continuity along the zeros
  have hza : riemannZeta a = 0 := by
    have hcont : Tendsto riemannZeta (nhds a) (nhds (riemannZeta a)) :=
      ((differentiableAt_riemannZeta ha1).continuousAt).tendsto
    have hcomp : Tendsto (fun k => riemannZeta (z (φ k))) atTop
        (nhds (riemannZeta a)) := hcont.comp htend
    have hzero : Tendsto (fun k => riemannZeta (z (φ k))) atTop (nhds 0) := by
      have : (fun k => riemannZeta (z (φ k))) = fun _ => (0 : ℂ) := by
        funext k
        exact (hz_zero (φ k)).1
      rw [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hcomp hzero
  -- strip-closure bounds from the rectangle
  have haRect := haK
  rw [Complex.mem_reProdIm] at haRect
  have hre0 : 0 ≤ a.re := haRect.1.1
  have hre1 : a.re ≤ 1 := haRect.1.2
  -- re a < 1 by the zero-free line
  have hlt1 : a.re < 1 := by
    rcases lt_or_eq_of_le hre1 with h | h
    · exact h
    · exact absurd hza (riemannZeta_ne_zero_of_one_le_re (by rw [h]))
  -- re a > 0 by functional-equation transfer to re = 1
  have hgt0 : 0 < a.re := by
    rcases lt_or_eq_of_le hre0 with h | h
    · exact h
    · exfalso
      have hn : ∀ n : ℕ, a ≠ -(n : ℂ) := by
        intro n hcontra
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rw [h0] at hcontra
          simp at hcontra
          exact ha0 hcontra
        · have : a.re = -(n : ℝ) := by rw [hcontra]; simp
          rw [← h] at this
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
          linarith
      have hz1a : riemannZeta (1 - a) = 0 := by
        rw [riemannZeta_one_sub hn ha1, hza, mul_zero]
      have hre1a : (1 : ℝ) ≤ (1 - a).re := by
        simp [Complex.sub_re, Complex.one_re]
        linarith
      exact riemannZeta_ne_zero_of_one_le_re hre1a hz1a
  -- a is a nontrivial zero whose pole point is x: contradiction
  exact hx ⟨a, ⟨hza, hgt0, hlt1⟩, hpa.symm⟩

#print axioms nonpole_isolated

end

end RHFormalization
