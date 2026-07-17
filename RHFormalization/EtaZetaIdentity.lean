/-
EtaZetaIdentity.lean — Real-zero-free campaign, Piece 1.
Eta-zeta algebraic identity infrastructure on re > 1.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open Complex Filter
open scoped Topology

namespace RHFormalization

/-- The zeta Dirichlet series is summable for `re s > 1` (indexed from 0 via `n+1`). -/
theorem summable_zeta_terms {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
  have h := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr (fun n => ?_)
  push_cast
  ring_nf

/-- Each even-index zeta term factors as `2^(-s)` times the corresponding zeta term. -/
theorem even_term_eq {s : ℂ} (n : ℕ) :
    1 / ((2 * n : ℂ) + 2) ^ s = (2 : ℂ) ^ (-s) * (1 / ((n : ℂ) + 1) ^ s) := by
  have hfac : ((2 * n : ℂ) + 2) = (2 : ℂ) * ((n : ℂ) + 1) := by ring
  have h2pos : (0 : ℝ) ≤ 2 := by norm_num
  have hnpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hsplit : ((2 : ℂ) * ((n : ℂ) + 1)) ^ s = (2 : ℂ) ^ s * ((n : ℂ) + 1) ^ s := by
    have : ((2 : ℂ) * ((n : ℂ) + 1)) = ((2 : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, mul_cpow_ofReal_nonneg h2pos hnpos]
    push_cast
    ring
  rw [hfac, hsplit, cpow_neg]
  have h2ne : (2 : ℂ) ^ s ≠ 0 := by
    apply cpow_ne_zero_iff.mpr; norm_num
  field_simp

/-- The even-denominator subsum equals `2^(-s)` times the zeta series. -/
theorem even_subsum_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, 1 / ((2 * (k:ℂ)) + 2) ^ s)
      = (2 : ℂ) ^ (-s) * (∑' k : ℕ, 1 / ((k:ℂ) + 1) ^ s) := by
  rw [← Summable.tsum_mul_left]
  · refine tsum_congr (fun k => ?_)
    exact even_term_eq k
  · exact summable_zeta_terms hs

/-- Summability of the even sub-series `f (2k)` where `f n = 1/(n+1)^s`. -/
theorem summable_even {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s) :=
  (summable_zeta_terms hs).comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))

/-- Summability of the odd sub-series `f (2k+1)`. -/
theorem summable_odd {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s) :=
  (summable_zeta_terms hs).comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))

#print axioms summable_zeta_terms
#print axioms even_term_eq
#print axioms even_subsum_eq
/-- The eta series splits as odd-index subsum minus even-index-shifted subsum. -/
theorem eta_split {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (-1 : ℂ) ^ n * (1 / ((n : ℂ) + 1) ^ s))
      = (∑' k : ℕ, 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s)
        - (∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s) := by
  set f : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * (1 / ((n : ℂ) + 1) ^ s) with hf
  have hev : Summable (fun k : ℕ => f (2 * k)) := by
    have hfe : (fun k : ℕ => f (2 * k))
        = (fun k : ℕ => 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s) := by
      funext k
      simp only [hf]
      rw [(even_two_mul k).neg_one_pow, one_mul]
    rw [hfe]; exact summable_even hs
  have hod : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have hfo : (fun k : ℕ => f (2 * k + 1))
        = (fun k : ℕ => -(1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s)) := by
      funext k
      simp only [hf]
      rw [(odd_two_mul_add_one k).neg_one_pow, neg_one_mul]
    rw [hfo]; exact (summable_odd hs).neg
  rw [← tsum_even_add_odd hev hod, sub_eq_add_neg, ← tsum_neg]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine tsum_congr (fun k => ?_)
    simp only [hf]
    rw [(even_two_mul k).neg_one_pow, one_mul]
  · refine tsum_congr (fun k => ?_)
    simp only [hf]
    rw [(odd_two_mul_add_one k).neg_one_pow, neg_one_mul]

/-- The zeta series splits as the odd-denominator subsum plus the even-denominator subsum. -/
theorem zeta_split {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s)
      = (∑' k : ℕ, 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s)
        + (∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s) := by
  set g : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hg
  have hev : Summable (fun k : ℕ => g (2 * k)) := summable_even hs
  have hod : Summable (fun k : ℕ => g (2 * k + 1)) := summable_odd hs
  rw [← tsum_even_add_odd hev hod]

#print axioms summable_even
#print axioms summable_odd
/-- The even-denominator subsum (from the `2k+1` index) matches the `even_subsum_eq` form. -/
theorem odd_index_subsum_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s)
      = (2 : ℂ) ^ (-s) * (∑' k : ℕ, 1 / ((k : ℂ) + 1) ^ s) := by
  rw [← even_subsum_eq hs]
  refine tsum_congr (fun k => ?_)
  congr 2
  push_cast
  ring

/-- THE ETA-ZETA IDENTITY on re > 1:  (1 - 2·2^(-s))·ζ(s) = η(s). -/
theorem eta_zeta_identity {s : ℂ} (hs : 1 < s.re) :
    (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s
      = ∑' n : ℕ, (-1 : ℂ) ^ n * (1 / ((n : ℂ) + 1) ^ s) := by
  have hz : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
    zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have heta := eta_split hs
  have hzeta := zeta_split hs
  have hodd := odd_index_subsum_eq hs
  rw [hz, heta]
  linear_combination hzeta + 2 * hodd

#print axioms eta_split
#print axioms zeta_split
#print axioms odd_index_subsum_eq
#print axioms eta_zeta_identity

end RHFormalization
