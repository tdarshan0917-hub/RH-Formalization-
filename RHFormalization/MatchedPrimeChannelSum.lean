-- SENTINEL: matched-prime-channel-sum-v1
import RHFormalization.MatchedSingleChannelResolvent
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module
open scoped BigOperators Classical

variable {N : ℕ}

/--
Finite sum of the fully interacting singleton response differences.

There is deliberately no outer arithmetic weight: each singleton
potential already contains exactly one copy of `ppWeightReal k`.
-/
def matchedPrimeChannelPerturbedDifference
    (μ : Fin N → ℝ) (ks : Finset ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ ks,
    (matchedSingleChannelPerturbedResponse
        (N := N) μ k L z
      -
     matchedSingleChannelFreeResponse
        (N := N) μ k L z)

/-- Finite sum of the matched first-Born channels. -/
def matchedPrimeChannelFirstBornSum
    (μ : Fin N → ℝ) (ks : Finset ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ ks,
    matchedSingleChannelFirstBorn
      (N := N) μ k L z

/--
Finite sum of the fully resummed singleton nonlinear remainders.

Each summand contains only one physical channel `k`; there are no
`k ≠ q` mixed-channel terms.
-/
def matchedPrimeChannelSecondRemainderSum
    (μ : Fin N → ℝ) (ks : Finset ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ ks,
    matchedSingleChannelSecondRemainder
      (N := N) μ k L z

/--
Exact finite matched-channel sum identity.

This is still pure finite-dimensional resolvent algebra:
no O3, no seam bound, no limit, and no provider assumption.
-/
theorem matchedPrimeChannel_sum_eq_first_plus_second
    (μ : Fin N → ℝ) (ks : Finset ℕ) (L : ℝ) (z : ℂ)
    (hneF : ∀ i, z + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ k ∈ ks, ∀ i,
      z + ((perturbedEigenvalues μ
        (matchedSingleChannelVC_isHermitian
          (N := N) k L) i : ℝ) : ℂ) ≠ 0) :
    matchedPrimeChannelPerturbedDifference
        (N := N) μ ks L z
      =
    matchedPrimeChannelFirstBornSum
        (N := N) μ ks L z
      +
    matchedPrimeChannelSecondRemainderSum
        (N := N) μ ks L z := by
  unfold matchedPrimeChannelPerturbedDifference
    matchedPrimeChannelFirstBornSum
    matchedPrimeChannelSecondRemainderSum
  calc
    (∑ k ∈ ks,
      (matchedSingleChannelPerturbedResponse
          (N := N) μ k L z
        -
       matchedSingleChannelFreeResponse
          (N := N) μ k L z))
        =
      ∑ k ∈ ks,
        (matchedSingleChannelFirstBorn
            (N := N) μ k L z
          +
         matchedSingleChannelSecondRemainder
            (N := N) μ k L z) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact
            matchedSingleChannel_response_eq_first_plus_second
              (N := N) μ k L z hneF (hneP k hk)
    _ =
      (∑ k ∈ ks,
        matchedSingleChannelFirstBorn
          (N := N) μ k L z)
      +
      ∑ k ∈ ks,
        matchedSingleChannelSecondRemainder
          (N := N) μ k L z := by
          rw [Finset.sum_add_distrib]

/--
The identity survives multiplication by any density-normalization scalar.

The live stage will instantiate `ρ` with `admDensityC n` or
`adaptiveDensityC c n`.
-/
theorem matchedPrimeChannel_scalar_mul_sum_eq_first_plus_second
    (ρ : ℂ)
    (μ : Fin N → ℝ) (ks : Finset ℕ) (L : ℝ) (z : ℂ)
    (hneF : ∀ i, z + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ k ∈ ks, ∀ i,
      z + ((perturbedEigenvalues μ
        (matchedSingleChannelVC_isHermitian
          (N := N) k L) i : ℝ) : ℂ) ≠ 0) :
    ρ *
      matchedPrimeChannelPerturbedDifference
        (N := N) μ ks L z
      =
    ρ *
      matchedPrimeChannelFirstBornSum
        (N := N) μ ks L z
      +
    ρ *
      matchedPrimeChannelSecondRemainderSum
        (N := N) μ ks L z := by
  rw [matchedPrimeChannel_sum_eq_first_plus_second
        (N := N) μ ks L z hneF hneP]
  ring

#print axioms matchedPrimeChannelPerturbedDifference
#print axioms matchedPrimeChannelFirstBornSum
#print axioms matchedPrimeChannelSecondRemainderSum
#print axioms matchedPrimeChannel_sum_eq_first_plus_second
#print axioms matchedPrimeChannel_scalar_mul_sum_eq_first_plus_second

end

end RHFormalization
