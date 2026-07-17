import Mathlib.NumberTheory.Chebyshev

/-!
# Prime-well envelope bound (DQ1), Lemma B: Chebyshev shell mass

The load-bearing arithmetic input for the cutoff-uniform prime-well potential bound.
For a dyadic block of integers, the von Mangoldt mass is bounded linearly via
Chebyshev's `psi_le_const_mul_self`.

This is the first brick of the DQ1 envelope proof: it establishes that the
arithmetic (prime-counting) content needed is exactly what Mathlib provides, with
the explicit Chebyshev constant `log 4 + 4`.
-/

namespace RHFormalization

open Chebyshev ArithmeticFunction Finset

/-- **Lemma B (Chebyshev shell mass).** The von Mangoldt mass over integers in
`Ioc 0 ⌊y⌋` is bounded by the Chebyshev constant times `y`, for `y ≥ 0`.
This is exactly `Chebyshev.psi x = ∑_{n ≤ x} Λ n` bounded by `(log 4 + 4) y`. -/
theorem vonMangoldt_partial_sum_le (y : ℝ) (hy : 0 ≤ y) :
    ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, vonMangoldt n ≤ (Real.log 4 + 4) * y := by
  have h := Chebyshev.psi_le_const_mul_self hy
  rwa [Chebyshev.psi] at h

/-- **Lemma B, shell form.** The von Mangoldt mass over a dyadic shell
`Ioc ⌊a⌋ ⌊b⌋` (integers between `a` and `b`) is bounded by the mass up to `b`,
hence by `(log 4 + 4) * b`. Used with `a = 2^k`, `b = 2^(k+1)`. -/
theorem vonMangoldt_shell_mass_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n ≤ (Real.log 4 + 4) * b := by
  have hsub : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ⊆ Finset.Ioc 0 ⌊b⌋₊ := by
    apply Finset.Ioc_subset_Ioc_left
    exact Nat.zero_le _
  calc ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ ≤ (Real.log 4 + 4) * b := vonMangoldt_partial_sum_le b hb

#print axioms vonMangoldt_partial_sum_le
#print axioms vonMangoldt_shell_mass_le

end RHFormalization
