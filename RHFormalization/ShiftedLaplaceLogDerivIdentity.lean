import RHFormalization.ShiftedLaplacePrimeSummable
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- Complex exp→cpow bridge: for a valid pair, `exp(-center · w) = natValue^(-w)`. -/
theorem exp_neg_center_eq_cpow
    (q : PrimePowerPair) (hq : IsPrimePowerPair q) (w : ℂ) :
    Complex.exp (-(q.center : ℂ) * w) = (q.natValue : ℂ) ^ (-w) := by
  have hpos : (0 : ℝ) < (q.natValue : ℝ) := by
    have : 1 ≤ q.natValue := Nat.one_le_iff_ne_zero.mpr (by
      simp only [PrimePowerPair.natValue]
      exact pow_ne_zero _ (Nat.Prime.ne_zero hq.1))
    exact_mod_cast lt_of_lt_of_le one_pos (by exact_mod_cast this)
  have hne : (q.natValue : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, PrimePowerPair.natValue]
    exact pow_ne_zero _ (Nat.Prime.ne_zero hq.1)
  rw [Complex.cpow_neg, Complex.cpow_def_of_ne_zero hne]
  rw [← Complex.exp_neg]
  congr 1
  -- -center * w  vs  -(w * log natValue);  center = Real.log natValue
  unfold PrimePowerPair.center
  rw [Complex.ofReal_log hpos.le]
  push_cast
  ring

/-- Term-level identity: on a valid pair, the Laplace prime term equals
`(1/(2√(s+¼))) · (von Mangoldt L-series term at √(s+¼)+½)`. -/
theorem laplace_term_eq_vonMangoldt_term
    (q : PrimePowerPair) (hq : IsPrimePowerPair q) (s : ℂ) :
    q.weightC * shiftedLaplaceHeatKernelC q.center s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) q.natValue := by
  set w : ℂ := Complex.sqrt (s + (1/4:ℂ)) with hw
  have hn1 : q.natValue ≠ 0 := by
    simp only [PrimePowerPair.natValue]; exact pow_ne_zero _ (Nat.Prime.ne_zero hq.1)
  have hne : (q.natValue : ℂ) ≠ 0 := by exact_mod_cast hn1
  -- LHS kernel value
  rw [shiftedLaplaceHeatKernelC_apply, ← hw]
  -- weightC = Λ(natValue)/√(natValue) on valid pairs
  have hweight : q.weightC = (ArithmeticFunction.vonMangoldt q.natValue : ℂ)
      / (q.natValue : ℂ) ^ (1/2 : ℂ) := by
    -- Λ(p^m) = Λ(p) = log p  (m ≠ 0, p prime); weightReal = log p / √(p^m)
    have hΛ : ArithmeticFunction.vonMangoldt q.natValue = Real.log q.p := by
      simp only [PrimePowerPair.natValue]
      rw [ArithmeticFunction.vonMangoldt_apply_pow hq.2.ne',
          ArithmeticFunction.vonMangoldt_apply_prime hq.1]
    have hpos : (0:ℝ) < (q.natValue : ℝ) := by
      have : 1 ≤ q.natValue := Nat.one_le_iff_ne_zero.mpr (by
        simp only [PrimePowerPair.natValue]; exact pow_ne_zero _ (Nat.Prime.ne_zero hq.1))
      exact_mod_cast lt_of_lt_of_le one_pos (by exact_mod_cast this)
    -- unfold weightC = (weightReal : ℂ), weightReal = log p / √(natValue) on valid
    unfold PrimePowerPair.weightC PrimePowerPair.weightReal
    rw [if_pos hq]
    push_cast [hΛ]
    -- goal: Complex.log ↑p / ↑√natValue = Complex.log ↑p / (natValue:ℂ)^(1/2)
    congr 1
    -- ↑(√(natValue:ℝ)) = (natValue:ℂ)^(1/2)
    rw [Real.sqrt_eq_rpow]
    rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (q.natValue:ℝ))]
    push_cast
    norm_num
  -- term value
  rw [LSeries.term_of_ne_zero hn1]
  rw [hweight, exp_neg_center_eq_cpow q hq w]
  -- now pure cpow algebra:  (Λ/n^½)·(1/2w)·n^(-w) = (1/2w)·(Λ·n^(-(w+½)))
  rw [Complex.cpow_neg, Complex.cpow_add _ _ hne]
  field_simp

end RHFormalization

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- The range of `natValue` on valid pairs is exactly the prime powers.
Surjectivity direction: every prime power is `natValue` of a valid pair. -/
theorem vonMangoldt_term_support_subset_range
    {w : ℂ} (n : ℕ)
    (hn : LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w n ≠ 0) :
    ∃ q : {q : PrimePowerPair // IsPrimePowerPair q}, q.1.natValue = n := by
  -- term ≠ 0 ⟹ n ≠ 0 and Λ n ≠ 0 ⟹ IsPrimePow n
  have hn0 : n ≠ 0 := by
    rintro rfl; simp [LSeries.term] at hn
  have hΛne : (ArithmeticFunction.vonMangoldt n : ℂ) ≠ 0 := by
    intro h; apply hn; rw [LSeries.term_of_ne_zero hn0, h, zero_div]
  have hΛne' : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro h; apply hΛne; rw [h]; simp
  have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛne'
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpp
  exact ⟨⟨(p, k), ⟨hp, hk⟩⟩, hpk⟩

/-- Reindex: the von Mangoldt L-series equals the sum over valid prime-power
pairs of the term composed with `natValue`. -/
theorem LSeries_vonMangoldt_eq_tsum_pairs
    {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w
      = ∑' q : {q : PrimePowerPair // IsPrimePowerPair q},
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w q.1.natValue := by
  set f : ℕ → ℂ := fun n =>
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w n with hf
  set g : {q : PrimePowerPair // IsPrimePowerPair q} → ℕ := fun q => q.1.natValue with hg
  have hinj : Function.Injective g := by
    intro a b hab; exact Subtype.ext (natValue_injOn_valid a.2 b.2 hab)
  have hsumm : Summable f := vonMangoldt_LSeriesSummable hw
  -- support of f ⊆ range g  (term ≠ 0 ⟹ prime power ⟹ in range)
  have hsupp : Function.support f ⊆ Set.range g := by
    intro n hn
    obtain ⟨q, hq⟩ := vonMangoldt_term_support_subset_range n hn
    exact ⟨q, hq⟩
  -- LSeries = ∑' n, f n = ∑' (range g), f = ∑' q, f (g q)
  rw [LSeries]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  -- ∑' (x : range g), f x = ∑' q, f (g q)  via the equiv range g ≃ domain
  exact (Equiv.ofInjective g hinj).tsum_eq (fun x => f x) |>.symm

end RHFormalization

namespace RHFormalization

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

/-- Piece (2): the shifted-Laplace prime package Bshared equals the shifted
zeta log-derivative on the half-plane `1 < (√(s+¼)+½).re`. -/
theorem shiftedLaplace_Bshared_eq_logDeriv
    {s : ℂ} (hw : 1 < (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)).re) :
    shiftedLaplacePrimePackage.Bshared s
      = - (1 / (2 * Complex.sqrt (s + (1/4:ℂ))))
          * (deriv riemannZeta (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))
              / riemannZeta (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))) := by
  classical
  set c : ℂ := 1 / (2 * Complex.sqrt (s + (1/4:ℂ))) with hc
  set w : ℂ := Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) with hwdef
  set Λc : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) with hΛc
  -- per-term identity: full-pair term = if valid then c * termΛ else 0
  have hterm_all : ∀ q : PrimePowerPair,
      q.weightC * shiftedLaplaceHeatKernelC q.center s
        = if IsPrimePowerPair q then c * LSeries.term Λc w q.natValue else 0 := by
    intro q
    by_cases hq : IsPrimePowerPair q
    · rw [if_pos hq, laplace_term_eq_vonMangoldt_term q hq s]
    · rw [if_neg hq]
      have hw0 : q.weightReal = 0 := by
        unfold PrimePowerPair.weightReal; rw [if_neg (by simpa using hq)]
      have hC0 : q.weightC = 0 := by unfold PrimePowerPair.weightC; rw [hw0]; simp
      rw [hC0, zero_mul]
  -- the if-sum over all pairs equals the sum over the valid subtype
  have hif_collapse :
      (∑' q : PrimePowerPair, if IsPrimePowerPair q then c * LSeries.term Λc w q.natValue else 0)
        = ∑' q : {q : PrimePowerPair // IsPrimePowerPair q},
            c * LSeries.term Λc w q.1.natValue := by
    rw [← tsum_subtype_eq_of_support_subset
          (f := fun q : PrimePowerPair =>
            if IsPrimePowerPair q then c * LSeries.term Λc w q.natValue else 0)
          (s := {q : PrimePowerPair | IsPrimePowerPair q}) ?_]
    · refine tsum_congr (fun q => ?_)
      have hq : IsPrimePowerPair (↑q) := q.2
      rw [if_pos hq]
    · intro q hq
      rw [Function.mem_support] at hq
      simp only [Set.mem_setOf_eq]
      by_contra hnv
      exact hq (if_neg hnv)
  calc shiftedLaplacePrimePackage.Bshared s
      = ∑' q : PrimePowerPair, q.weightC * shiftedLaplaceHeatKernelC q.center s :=
        shiftedLaplacePrimePackage_Bshared_eq_tsum s
    _ = ∑' q : PrimePowerPair,
          (if IsPrimePowerPair q then c * LSeries.term Λc w q.natValue else 0) :=
        tsum_congr hterm_all
    _ = ∑' q : {q : PrimePowerPair // IsPrimePowerPair q},
          c * LSeries.term Λc w q.1.natValue := hif_collapse
    _ = c * ∑' q : {q : PrimePowerPair // IsPrimePowerPair q},
          LSeries.term Λc w q.1.natValue := tsum_mul_left
    _ = c * LSeries Λc w := by rw [← LSeries_vonMangoldt_eq_tsum_pairs hw]
    _ = c * (- deriv riemannZeta w / riemannZeta w) := by
        rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
    _ = - c * (deriv riemannZeta w / riemannZeta w) := by ring

end RHFormalization
