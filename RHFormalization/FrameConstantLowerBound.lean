import Mathlib

/-!
# FrameConstantLowerBound — K1 of the raw-Gaussian frame obstruction

Generic inner-product fact: a family whose members pairwise overlap by at
least `α > 0` on a finite subfamily `S` has `‖Σ_S v‖² ≥ α·|S|²`. Hence any
Bessel constant valid for arbitrary coefficients on that family is at least
`α·|S|`. Pure Hilbert-space algebra; kills only the raw-channel generic-Bessel
route, nothing broader.
-/

set_option autoImplicit false

namespace RHFormalization

open Finset

/-- **K1a — Gram lower bound.** -/
theorem norm_sq_sum_ge_of_inner_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (S : Finset ι) (v : ι → E) (α : ℝ)
    (h : ∀ i ∈ S, ∀ j ∈ S, α ≤ inner ℝ (v i) (v j)) :
    α * (S.card : ℝ) ^ 2 ≤ ‖∑ i ∈ S, v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum]
  calc
    α * (S.card : ℝ) ^ 2
        = ∑ i ∈ S, ∑ j ∈ S, α := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, inner ℝ (v i) (v j) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact Finset.sum_le_sum (fun j hj => h i hi j hj)

/-- **K1b — Bessel-constant lower bound.** -/
theorem bessel_const_ge_of_inner_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (S : Finset ι) (v : ι → E) (α B : ℝ)
    (hB : ∀ c : ι → ℝ,
      ‖∑ i ∈ S, c i • v i‖ ^ 2 ≤ B * ∑ i ∈ S, c i ^ 2)
    (h : ∀ i ∈ S, ∀ j ∈ S, α ≤ inner ℝ (v i) (v j))
    (hS : 0 < S.card) :
    α * (S.card : ℝ) ≤ B := by
  have h1 := norm_sq_sum_ge_of_inner_ge S v α h
  have h2 := hB (fun _ => 1)
  simp only [one_smul, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one] at h2
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS
  have h3 : α * (S.card : ℝ) * (S.card : ℝ) ≤ B * (S.card : ℝ) := by
    nlinarith [h1, h2]
  exact le_of_mul_le_mul_right h3 hc

#print axioms norm_sq_sum_ge_of_inner_ge
#print axioms bessel_const_ge_of_inner_ge

end RHFormalization
