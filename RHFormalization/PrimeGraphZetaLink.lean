import RHFormalization.PrimeGraphEulerSplit
import RHFormalization.PrimePowerSumConvergence
import Mathlib

/-!
# PrimeGraphZetaLink — PG-9a/b: the graph's Euler part is a truncated von Mangoldt series

* `vonMangoldt_term_primePow`: the L-series term of Λ at `p^{k+1}` is `log p · (p^{-s})^{k+1}`.
* `euler_factor_hasSum`: `Σ_{k≥0} term(p^{k+1}) = log p · p^{-s}/(1-p^{-s})` for `Re s > 0`.
* `euler_factor_indicator_hasSum`: the same as a sum over all `n`, restricted to powers of `p`.
* `truncated_vonMangoldt_hasSum` (PG-9b): for a finite set `S` of primes, the von Mangoldt
  series restricted to powers of primes in `S` sums to `Σ_{p∈S} log p · p^{-s}/(1-p^{-s})` —
  exactly the Euler part of PG-8 (with `p^{-s} = p^{ix-1/2}`).
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

theorem vonMangoldt_term_primePow {p : ℕ} (hp : p.Prime) (s : ℂ) (k : ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s (p ^ (k + 1))
      = (Real.log p : ℂ) * ((p : ℂ) ^ (-s)) ^ (k + 1) := by
  have hn : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hn, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpow : ((p : ℂ) ^ (k + 1)) ^ s = ((p : ℂ) ^ s) ^ (k + 1) := by
    rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  rw [Nat.cast_pow, hpow, Complex.cpow_neg, inv_pow, div_eq_mul_inv]

theorem primeCpow_neg_norm_lt_one {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  first
    | rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    | rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by rw [Complex.neg_re]; linarith),
        Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- **PG-9a — one Euler factor.** -/
theorem euler_factor_hasSum {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
        (p ^ (k + 1)))
      ((Real.log p : ℂ) * ((p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)))) := by
  have hg := (hasSum_geometric_of_norm_lt_one (primeCpow_neg_norm_lt_one hp hs)).mul_left
    ((Real.log p : ℂ) * (p : ℂ) ^ (-s))
  have hf : (fun k : ℕ => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
        (p ^ (k + 1)))
      = fun k : ℕ => (Real.log p : ℂ) * (p : ℂ) ^ (-s) * ((p : ℂ) ^ (-s)) ^ k := by
    funext k
    rw [vonMangoldt_term_primePow hp, pow_succ']
    ring
  rw [hf, div_eq_mul_inv, ← mul_assoc]
  exact hg

theorem euler_factor_indicator_hasSum {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    HasSum (Set.indicator (Set.range fun k : ℕ => p ^ (k + 1))
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s))
      ((Real.log p : ℂ) * ((p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)))) := by
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := by
    intro a b hab
    have h := Nat.pow_right_injective hp.two_le hab
    omega
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    first
      | exact Set.indicator_of_notMem hn _
      | exact Set.indicator_of_not_mem hn _
      | simp [Set.indicator_apply, hn]
  · have hcomp : (Set.indicator (Set.range fun k : ℕ => p ^ (k + 1))
          (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s)) ∘
          (fun k : ℕ => p ^ (k + 1))
        = fun k : ℕ => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
            (p ^ (k + 1)) := by
      funext k
      exact Set.indicator_of_mem (Set.mem_range_self k) _
    rw [hcomp]
    exact euler_factor_hasSum hp hs

/-- **PG-9b — truncated von Mangoldt series = graph Euler part.** -/
theorem truncated_vonMangoldt_hasSum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n => ∑ p ∈ S, Set.indicator (Set.range fun k : ℕ => p ^ (k + 1))
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) n)
      (∑ p ∈ S, (Real.log p : ℂ) * ((p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)))) :=
  hasSum_sum (fun p hp => euler_factor_indicator_hasSum (hS p hp) hs)

#print axioms vonMangoldt_term_primePow
#print axioms euler_factor_hasSum
#print axioms euler_factor_indicator_hasSum
#print axioms truncated_vonMangoldt_hasSum

end RHFormalization
