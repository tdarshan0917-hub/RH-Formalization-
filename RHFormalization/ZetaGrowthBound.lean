import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# RHFormalization.ZetaGrowthBound

Pillar 2 of `hsum`: growth bounds toward the Riemann–von Mangoldt zero-counting estimate.
This file is the START of the growth-bound chain:
  ‖Γ(s)‖ bound → ‖ξ(s)‖ growth (order 1) → Jensen → N(T) = O(T log T).

First brick: `‖Γ(s)‖ ≤ Γ_ℝ(re s)` for `0 < re s`, by bounding the Euler integral
`‖∫ e^{-x} x^{s-1}‖ ≤ ∫ e^{-x} x^{re s - 1} = Γ_ℝ(re s)`.

Isolated file; touches nothing else.
-/

namespace RHFormalization

open MeasureTheory Real Set Complex

/-- **First growth brick:** the complex Gamma is bounded in norm by the real Gamma of the
real part, on the right half-plane. -/
theorem norm_Gamma_le_real_Gamma {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [Real.Gamma_eq_integral hs]
  apply le_of_eq
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hxpos : (0 : ℝ) < x := hx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.one_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

#print axioms norm_Gamma_le_real_Gamma

/-- **Brick 2: Γ is bounded uniformly in the imaginary direction.** For fixed real part `σ > 0`,
`‖Γ(σ + it)‖ ≤ Γ_ℝ(σ)` for every `t` — the bound does not depend on `t`. Immediate from brick 1,
since the right-hand side depends only on the real part. -/
theorem norm_Gamma_vertical_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖Complex.Gamma (σ + t * Complex.I)‖ ≤ Real.Gamma σ := by
  have hre : (σ + t * Complex.I).re = σ := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      add_zero]
  have hpos : 0 < (σ + t * Complex.I).re := by rw [hre]; exact hσ
  have hb := norm_Gamma_le_real_Gamma hpos
  rwa [hre] at hb

#print axioms norm_Gamma_vertical_le

/-- `Real.Gamma` is continuous on `[a,b]` when `0 < a` (no non-positive-integer poles there). -/
theorem real_Gamma_continuousOn_Icc {a b : ℝ} (ha : 0 < a) :
    ContinuousOn Real.Gamma (Set.Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
  refine (Real.differentiableAt_Gamma ?_).continuousAt
  intro m hcontra
  -- x = -↑m with x > 0 and ↑m ≥ 0 is a contradiction
  have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [hcontra] at hxpos
  linarith

/-- **Brick 3: uniform vertical-strip bound for Γ.** For `0 < a ≤ re s ≤ b`, `‖Γ(s)‖` is bounded
by the maximum of `Γ_ℝ` over the compact interval `[a,b]` — a bound independent of `im s`.
Combines brick 1 (`‖Γ(s)‖ ≤ Γ_ℝ(re s)`) with continuity of `Γ_ℝ` on `[a,b]`. -/
theorem norm_Gamma_strip_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖Complex.Gamma s‖ ≤ C := by
  -- Γ_ℝ continuous on compact [a,b] attains a max at some c.
  obtain ⟨c, hc_mem, hc_max⟩ := (isCompact_Icc).exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) (real_Gamma_continuousOn_Icc ha)
  refine ⟨Real.Gamma c, ?_, ?_⟩
  · have hcpos : 0 < c := lt_of_lt_of_le ha hc_mem.1
    exact (Real.Gamma_pos_of_pos hcpos).le
  · -- ‖Γ(s)‖ ≤ Γ_ℝ(re s) ≤ Γ_ℝ(c) = max
    have hsre_mem : s.re ∈ Set.Icc a b := ⟨h1, h2⟩
    have hb1 : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re :=
      norm_Gamma_le_real_Gamma (lt_of_lt_of_le ha h1)
    exact hb1.trans (hc_max hsre_mem)

#print axioms norm_Gamma_strip_le

/-! ## Step 2: Γ growth via the recursion. The engine is `‖Γ(s+1)‖ = ‖s‖·‖Γ(s)‖`,
iterated to push from a bounded strip out to large real part, accumulating a `∏‖s+k‖`
factor that yields the order-1 (`‖s‖ log‖s‖`) growth. -/

/-- **Step-2 brick 1 (the recursion engine):** `‖Γ(s+1)‖ = ‖s‖ · ‖Γ(s)‖`. -/
theorem norm_Gamma_add_one (s : ℂ) (hs : s ≠ 0) :
    ‖Complex.Gamma (s + 1)‖ = ‖s‖ * ‖Complex.Gamma s‖ := by
  rw [Complex.Gamma_add_one s hs, norm_mul]

#print axioms norm_Gamma_add_one

/-- **Step-2 brick 2 (iterated recursion):** for `n : ℕ`,
`‖Γ(s+n)‖ = (∏ k ∈ range n, ‖s+k‖) · ‖Γ(s)‖`, provided `s+k ≠ 0` for all `k < n`. -/
theorem norm_Gamma_add_nat (s : ℂ) :
    ∀ n : ℕ, (∀ k : ℕ, k < n → s + k ≠ 0) →
      ‖Complex.Gamma (s + n)‖ = (∏ k ∈ Finset.range n, ‖s + (k : ℂ)‖) * ‖Complex.Gamma s‖ := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hk
    have hm : ∀ k : ℕ, k < m → s + (k : ℂ) ≠ 0 := fun k hkm => hk k (Nat.lt_succ_of_lt hkm)
    have hsm : s + (m : ℂ) ≠ 0 := hk m (Nat.lt_succ_self m)
    have hstep : ‖Complex.Gamma (s + (m : ℂ) + 1)‖ = ‖s + (m : ℂ)‖ * ‖Complex.Gamma (s + (m : ℂ))‖ :=
      norm_Gamma_add_one (s + (m : ℂ)) hsm
    have hcast : s + ((m : ℕ) + 1 : ℕ) = s + (m : ℂ) + 1 := by push_cast; ring
    rw [hcast, hstep, ih hm, Finset.prod_range_succ]
    ring

#print axioms norm_Gamma_add_nat

/-- Each factor is bounded: `‖s + k‖ ≤ ‖s‖ + n` for `k < n`. -/
theorem norm_add_nat_le (s : ℂ) {k n : ℕ} (hkn : k < n) :
    ‖s + (k : ℂ)‖ ≤ ‖s‖ + (n : ℝ) := by
  calc ‖s + (k : ℂ)‖ ≤ ‖s‖ + ‖(k : ℂ)‖ := norm_add_le _ _
    _ = ‖s‖ + (k : ℝ) := by rw [RCLike.norm_natCast]
    _ ≤ ‖s‖ + (n : ℝ) := by
        have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn.le
        linarith

/-- **Step-2 brick 3 (product bound):** `∏_{k<n} ‖s+k‖ ≤ (‖s‖ + n)^n`. Proved by induction:
each factor is `≤ ‖s‖ + n` (triangle inequality), and there are `n` of them. -/
theorem prod_norm_add_le (s : ℂ) (n : ℕ) :
    (∏ k ∈ Finset.range n, ‖s + (k : ℂ)‖) ≤ (‖s‖ + (n : ℝ)) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, pow_succ]
    have hfac0 := norm_add_nat_le s (Nat.lt_succ_self m)
    have hfac : ‖s + (m : ℂ)‖ ≤ ‖s‖ + ((m : ℝ) + 1) := by push_cast at hfac0 ⊢; linarith
    -- product so far ≤ (‖s‖+m)^m ≤ (‖s‖+(m+1))^m, times the new factor ≤ (‖s‖+(m+1))
    have hbase_nonneg : (0:ℝ) ≤ ‖s‖ + (m : ℝ) := by positivity
    have hmono : (‖s‖ + (m : ℝ)) ^ m ≤ (‖s‖ + ((m : ℝ) + 1)) ^ m :=
      pow_le_pow_left₀ hbase_nonneg (by linarith) m
    have hprod_nonneg : (0:ℝ) ≤ ∏ k ∈ Finset.range m, ‖s + (k : ℂ)‖ :=
      Finset.prod_nonneg (fun k _ => norm_nonneg _)
    have hfac_nonneg : (0:ℝ) ≤ ‖s + (m : ℂ)‖ := norm_nonneg _
    have hpow_nonneg : (0:ℝ) ≤ (‖s‖ + ((m : ℝ) + 1)) ^ m := by positivity
    push_cast
    calc (∏ k ∈ Finset.range m, ‖s + (k : ℂ)‖) * ‖s + (m : ℂ)‖
        ≤ (‖s‖ + ((m:ℝ)+1)) ^ m * ‖s + (m : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_right _ hfac_nonneg
          exact ih.trans hmono
      _ ≤ (‖s‖ + ((m:ℝ)+1)) ^ m * (‖s‖ + ((m:ℝ)+1)) := by
          apply mul_le_mul_of_nonneg_left hfac hpow_nonneg

#print axioms prod_norm_add_le

/-- **Step-2 brick 4 (Γ shift bound):** `‖Γ(s+n)‖ ≤ (‖s‖+n)^n · ‖Γ(s)‖`, provided `s+k ≠ 0`
for all `k < n`. Combines the iterated recursion (equality) with the product bound. -/
theorem norm_Gamma_add_nat_le (s : ℂ) (n : ℕ) (hk : ∀ k : ℕ, k < n → s + k ≠ 0) :
    ‖Complex.Gamma (s + n)‖ ≤ (‖s‖ + (n : ℝ)) ^ n * ‖Complex.Gamma s‖ := by
  rw [norm_Gamma_add_nat s n hk]
  apply mul_le_mul_of_nonneg_right (prod_norm_add_le s n) (norm_nonneg _)

#print axioms norm_Gamma_add_nat_le

end RHFormalization
