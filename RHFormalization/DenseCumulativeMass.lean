/-
DENSE SCHEDULE — Brick D3a: cumulative weighted mass, ℕ side (Lemma 1 core).
Σ_{1 < n ≤ 2^(K+1)} Λ(n)/√n ≤ 6(log4+4)·√(2^(K+1)), by induction on K,
summing the certified `weighted_shell_bound` over dyadic shells.
Step constant: 8 ≤ 6√2. No PNT, no new imports of strength.
D3b (next brick) bridges S1mass into this sum via the natValue injection.
-/

import RHFormalization.PrimeWellEnvelopeLemmaC

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

open ArithmeticFunction Finset Real

/-- `8 ≤ 6·√2` (equivalent to `16/9 ≤ 2`). -/
theorem eight_le_six_sqrt_two : (8 : ℝ) ≤ 6 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sqrt_nonneg (2 : ℝ), sq_nonneg (Real.sqrt 2 - 3/2)]

/-- **D3a — cumulative weighted mass over the dyadic tower.** -/
theorem cumulative_weighted_shell_bound (K : ℕ) :
    ∑ n ∈ Finset.Ioc 1 (2^(K+1)), vonMangoldt n / Real.sqrt n
      ≤ 6 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1)) := by
  have hB : (0:ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  induction K with
  | zero =>
      have h := weighted_shell_bound 0
      have hIoc : Finset.Ioc 1 (2^(0+1)) = Finset.Ioc (2^0) (2^(0+1)) := by
        norm_num
      rw [hIoc]
      refine le_trans h ?_
      have hs1 : Real.sqrt ((2:ℝ)^0) = 1 := by norm_num
      have hs2 : (1:ℝ) ≤ Real.sqrt ((2:ℝ)^(0+1)) := by
        rw [show ((2:ℝ)^(0+1)) = 2 by norm_num]
        have : (1:ℝ) = Real.sqrt 1 := by simp
        rw [this]
        exact Real.sqrt_le_sqrt (by norm_num)
      calc 2 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^0)
          = 2 * (Real.log 4 + 4) := by rw [hs1]; ring
        _ ≤ 6 * (Real.log 4 + 4) * 1 := by nlinarith
        _ ≤ 6 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(0+1)) := by
            apply mul_le_mul_of_nonneg_left hs2 (by nlinarith)
  | succ K ih =>
      -- split (1, 2^(K+2)] = (1, 2^(K+1)] ∪ (2^(K+1), 2^(K+2)]
      have h1le : (1:ℕ) ≤ 2^(K+1) := Nat.one_le_two_pow
      have h2le : (2:ℕ)^(K+1) ≤ 2^(K+2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hsplit : Finset.Ioc 1 (2^(K+2))
          = Finset.Ioc 1 (2^(K+1)) ∪ Finset.Ioc (2^(K+1)) (2^(K+2)) := by
        rw [Finset.Ioc_union_Ioc_eq_Ioc h1le h2le]
      have hdisj : Disjoint (Finset.Ioc 1 (2^(K+1)))
          (Finset.Ioc (2^(K+1)) (2^(K+2))) := by
        first
          | exact Finset.Ioc_disjoint_Ioc_consecutive 1 (2^(K+1)) (2^(K+2))
          | (apply Finset.disjoint_left.mpr
             intro a ha hb
             have h1 := (Finset.mem_Ioc.mp ha).2
             have h2 := (Finset.mem_Ioc.mp hb).1
             omega)
      have hshell := weighted_shell_bound (K+1)
      have hsum : ∑ n ∈ Finset.Ioc 1 (2^(K+2)), vonMangoldt n / Real.sqrt n
          = (∑ n ∈ Finset.Ioc 1 (2^(K+1)), vonMangoldt n / Real.sqrt n)
            + ∑ n ∈ Finset.Ioc (2^(K+1)) (2^(K+2)), vonMangoldt n / Real.sqrt n := by
        rw [hsplit, Finset.sum_union hdisj]
      rw [hsum]
      have hstep : (∑ n ∈ Finset.Ioc 1 (2^(K+1)), vonMangoldt n / Real.sqrt n)
            + ∑ n ∈ Finset.Ioc (2^(K+1)) (2^(K+2)), vonMangoldt n / Real.sqrt n
          ≤ 6 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1))
            + 2 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1)) := by
        apply add_le_add ih
        exact hshell
      refine le_trans hstep ?_
      -- 8B√(2^(K+1)) ≤ 6B√(2^(K+2)) since √(2^(K+2)) = √2·√(2^(K+1))
      have hs0 : (0:ℝ) ≤ (2:ℝ)^(K+1) := by positivity
      have hfact : Real.sqrt ((2:ℝ)^(K+2)) = Real.sqrt 2 * Real.sqrt ((2:ℝ)^(K+1)) := by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      have hsq : (0:ℝ) ≤ Real.sqrt ((2:ℝ)^(K+1)) := Real.sqrt_nonneg _
      calc 6 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1))
            + 2 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1))
          = 8 * ((Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1))) := by ring
        _ ≤ 6 * Real.sqrt 2 * ((Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1))) := by
            apply mul_le_mul_of_nonneg_right eight_le_six_sqrt_two
            exact mul_nonneg hB hsq
        _ = 6 * (Real.log 4 + 4) * (Real.sqrt 2 * Real.sqrt ((2:ℝ)^(K+1))) := by ring
        _ = 6 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+2)) := by rw [hfact]

#print axioms eight_le_six_sqrt_two
#print axioms cumulative_weighted_shell_bound

end RHFormalization
