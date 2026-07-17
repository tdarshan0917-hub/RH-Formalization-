import RHFormalization.PrimeSideTransformKernelPrototype
import RHFormalization.PrimePowerSumConvergence
import RHFormalization.PrimePowerWeightNormalizationLock
import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# RHFormalization.ShiftedLaplacePrimeSummable
**Option B, piece (1): right-half-plane convergence of the shifted-Laplace prime sum.**

On the region where `σ := (Complex.sqrt (s + 1/4)).re > 1/2`, the prime-power sum
`∑' q, weightC q * shiftedLaplaceHeatKernelC q.center s` converges absolutely.

This is the convergence the displacement kernel could never have (it was constant);
here it holds because the kernel genuinely decays like `(p^m)^{-σ}`.
No `sorry`.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex Filter Topology
open scoped BigOperators

/-- Norm of the shifted-Laplace kernel at a real center `a ≥ 0`:
`‖K a s‖ = (1/‖2√(s+¼)‖) * exp(-a * σ)` where `σ = Re √(s+¼)`. -/
theorem norm_shiftedLaplaceHeatKernelC
    (a : ℝ) (s : ℂ) :
    ‖shiftedLaplaceHeatKernelC a s‖
      = (1 / ‖2 * Complex.sqrt (s + (1/4 : ℂ))‖)
          * Real.exp (-a * (Complex.sqrt (s + (1/4 : ℂ))).re) := by
  unfold shiftedLaplaceHeatKernelC
  rw [norm_mul, norm_div, norm_one]
  congr 1
  rw [norm_exp]
  congr 1
  simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

end RHFormalization

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- On a valid prime-power pair, `Real.exp (-center · σ) = (natValue)^(-σ)`. -/
theorem exp_neg_center_eq_rpow
    (q : PrimePowerPair) (hq : IsPrimePowerPair q) (σ : ℝ) :
    Real.exp (-(q.center) * σ) = (q.natValue : ℝ) ^ (-σ) := by
  have hnv : (1 : ℝ) ≤ (q.natValue : ℝ) := by
    have : 1 ≤ q.natValue := Nat.one_le_iff_ne_zero.mpr (by
      simp only [PrimePowerPair.natValue]
      exact pow_ne_zero _ (Nat.Prime.ne_zero hq.1))
    exact_mod_cast this
  have hpos : (0 : ℝ) < (q.natValue : ℝ) := lt_of_lt_of_le one_pos hnv
  unfold PrimePowerPair.center PrimePowerPair.natValue
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

end RHFormalization

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- `natValue` is injective on valid prime-power pairs. -/
theorem natValue_injOn_valid
    {q q' : PrimePowerPair}
    (hq : IsPrimePowerPair q) (hq' : IsPrimePowerPair q')
    (h : q.natValue = q'.natValue) :
    q = q' := by
  obtain ⟨hp, hm⟩ := hq
  obtain ⟨hp', hm'⟩ := hq'
  have hval : q.p ^ q.m = q'.p ^ q'.m := h
  have hpe : q.p = q'.p := by
    have e1 : Nat.minFac (q.p ^ q.m) = q.p := hp.pow_minFac hm.ne'
    have e2 : Nat.minFac (q'.p ^ q'.m) = q'.p := hp'.pow_minFac hm'.ne'
    rw [← e1, ← e2, hval]
  have hme : q.m = q'.m := by
    rw [hpe] at hval
    exact Nat.pow_right_injective hp'.two_le hval
  exact Prod.ext hpe hme

end RHFormalization

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- Brick 1, transferred: over the valid prime-power subtype, the von Mangoldt term
at `w` with `1 < w.re` composed with `natValue` is summable. -/
theorem vonMangoldt_term_comp_natValue_summable
    {w : ℂ} (hw : 1 < w.re) :
    Summable (fun q : {q : PrimePowerPair // IsPrimePowerPair q} =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w (q.1.natValue)) := by
  have hbrick : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w) :=
    vonMangoldt_LSeriesSummable hw
  have hinj : Function.Injective
      (fun q : {q : PrimePowerPair // IsPrimePowerPair q} => q.1.natValue) := by
    intro a b hab
    exact Subtype.ext (natValue_injOn_valid a.2 b.2 hab)
  exact hbrick.comp_injective hinj

end RHFormalization

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- On the valid subtype, the Laplace prime-term norm is a constant multiple of the
von Mangoldt term norm at `σ + 1/2`. Hence summable over the valid subtype. -/
theorem laplace_norm_summable_on_valid
    {s : ℂ} (hs : (1:ℝ)/2 < (Complex.sqrt (s + (1/4:ℂ))).re) :
    Summable (fun q : {q : PrimePowerPair // IsPrimePowerPair q} =>
      ‖q.1.weightC * shiftedLaplaceHeatKernelC q.1.center s‖) := by
  set σ := (Complex.sqrt (s + (1/4:ℂ))).re with hσ
  set w : ℂ := (σ : ℂ) + (1/2 : ℂ) with hw_def
  have hwre : (1:ℝ) < w.re := by
    rw [hw_def]; simp [Complex.add_re, Complex.ofReal_re]; linarith
  have hStageA := vonMangoldt_term_comp_natValue_summable hwre
  -- the Laplace norm term = (1/‖2√‖) * ‖vonMangoldt term at w (natValue)‖
  have hC : (0:ℝ) ≤ 1 / ‖2 * Complex.sqrt (s + (1/4:ℂ))‖ := by positivity
  apply (hStageA.norm.mul_left (1 / ‖2 * Complex.sqrt (s + (1/4:ℂ))‖)).of_nonneg_of_le
    (fun q => norm_nonneg _)
  intro q
  have hq := q.2
  obtain ⟨hp, hm⟩ := hq
  -- abbreviations
  set n : ℕ := q.1.natValue with hn_def
  have hn1 : 1 ≤ n := by
    rw [hn_def]; exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [PrimePowerPair.natValue]; exact pow_ne_zero _ hp.ne_zero)
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  -- LHS: ‖weightC‖ * ‖K‖ = |weightReal| * (C * exp(-center*σ))
  rw [norm_mul, q.1.weightC_eq_coe_weightReal, Complex.norm_real,
      norm_shiftedLaplaceHeatKernelC]
  -- RHS majorant value
  have hterm : ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w n‖
      = ArithmeticFunction.vonMangoldt n / (n:ℝ) ^ w.re := by
    rw [LSeries.norm_term_eq]
    rw [if_neg (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn1)]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  -- weightReal value
  have hwr : |q.1.weightReal| = Real.log q.1.p / Real.sqrt (n:ℝ) := by
    rw [PrimePowerPair.weightReal, if_pos ⟨hp, hm⟩, abs_of_nonneg (by positivity), hn_def]
  -- vonMangoldt(n) = log p
  have hvm : (ArithmeticFunction.vonMangoldt n : ℝ) = Real.log q.1.p := by
    rw [hn_def]
    show (ArithmeticFunction.vonMangoldt (q.1.p ^ q.1.m) : ℝ) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow hm.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
  -- exp(-center*σ) = n^(-σ)
  have hexp : Real.exp (-(q.1.center) * σ) = (n:ℝ) ^ (-σ) := by
    rw [hn_def]; exact exp_neg_center_eq_rpow q.1 ⟨hp, hm⟩ σ
  rw [hterm, hvm]
  simp only [Real.norm_eq_abs, ← hσ]
  rw [hwr, hexp]
  have hwre' : w.re = σ + 1/2 := by rw [hw_def]; simp [Complex.add_re, Complex.ofReal_re]
  rw [hwre']
  apply le_of_eq
  rw [Real.sqrt_eq_rpow,
      show (n:ℝ) ^ (σ + 1/2) = (n:ℝ)^σ * (n:ℝ)^(1/2:ℝ) from Real.rpow_add hnpos _ _,
      Real.rpow_neg hnpos.le]
  field_simp

end RHFormalization

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- The full Laplace prime-term norm function over all of `PrimePowerPair`
is summable: invalid pairs contribute zero (weightReal = 0), so the support
sits inside the valid subtype, where summability was established. -/
theorem laplace_norm_summable_full
    {s : ℂ} (hs : (1:ℝ)/2 < (Complex.sqrt (s + (1/4:ℂ))).re) :
    Summable (fun q : PrimePowerPair =>
      ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖) := by
  have hsupp : Function.support
      (fun q : PrimePowerPair => ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖)
      ⊆ {q : PrimePowerPair | IsPrimePowerPair q} := by
    intro q hq
    by_contra hnv
    have hw0 : q.weightReal = 0 := by
      unfold PrimePowerPair.weightReal
      rw [if_neg (by simpa using hnv : ¬ IsPrimePowerPair q)]
    have hwC0 : q.weightC = 0 := by
      unfold PrimePowerPair.weightC; rw [hw0, Complex.ofReal_zero]
    -- q ∈ support means the term ≠ 0; but weightC q = 0 makes it 0
    rw [Function.mem_support] at hq
    apply hq
    rw [hwC0, zero_mul, norm_zero]
  have hvalid := laplace_norm_summable_on_valid hs
  -- hvalid : Summable (fun q : {q // IsPrimePowerPair q} => ‖(↑q).weightC * K (↑q).center s‖)
  -- transport to full type: term is zero off the valid set
  obtain ⟨a, ha⟩ := hvalid
  exact ⟨a, (hasSum_subtype_iff_of_support_subset hsupp).mp ha⟩

/-- Piece (1) complete: the Laplace Bshared prime sum converges absolutely
on the right half-plane, over the full index type. -/
theorem laplace_prime_summable_full
    {s : ℂ} (hs : (1:ℝ)/2 < (Complex.sqrt (s + (1/4:ℂ))).re) :
    Summable (fun q : PrimePowerPair =>
      q.weightC * shiftedLaplaceHeatKernelC q.center s) :=
  summable_norm_iff.mp (laplace_norm_summable_full hs)

end RHFormalization
