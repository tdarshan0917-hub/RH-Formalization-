import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Brick 2, Stone 7': the sharp s^{-1/2} heat-kernel sum bound
`∑_{m:Fin N} e^{-b(m+1)²} ≤ √(π/b)/2`, uniform in N. Integrable heat bound
(~b^{-1/2}); antitone Gaussian sum vs its integral. Makes the Duhamel time
integral converge (finite Beta integral).
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real MeasureTheory Set
open scoped BigOperators

variable {N : ℕ}

/-- `x ↦ e^{-b x²}` is antitone on `[x₀, x₀+a]` for `b ≥ 0`, `x₀ ≥ 0`. -/
theorem antitoneOn_gaussian (b : ℝ) (hb : 0 ≤ b) (x₀ a : ℝ) (hx₀ : 0 ≤ x₀) :
    AntitoneOn (fun x : ℝ => Real.exp (-b * x ^ 2)) (Icc x₀ (x₀ + a)) := by
  intro x hx y hy hxy
  simp only
  apply Real.exp_le_exp.mpr
  have hx0 : 0 ≤ x := le_trans hx₀ hx.1
  have : x ^ 2 ≤ y ^ 2 := by nlinarith [hx.1, hy.1, hx₀]
  nlinarith [hb, this]

/-- Bound `∫ 0..0+N e^{-bx²} ≤ √(π/b)/2`. -/
theorem integral_zero_N_gaussian_le (b : ℝ) (hb : 0 < b) :
    ∫ x in (0:ℝ)..(0 + (N:ℝ)), Real.exp (-b * x ^ 2) ≤ Real.sqrt (Real.pi / b) / 2 := by
  rw [zero_add]
  have hInt : ∫ x in Ioi (0:ℝ), Real.exp (-b * x ^ 2) = Real.sqrt (Real.pi / b) / 2 :=
    integral_gaussian_Ioi b
  rw [← hInt, intervalIntegral.integral_of_le (by positivity)]
  refine setIntegral_mono_set (integrable_exp_neg_mul_sq hb).integrableOn
    (Filter.Eventually.of_forall (fun x => le_of_lt (Real.exp_pos _))) ?_
  exact HasSubset.Subset.eventuallyLE Set.Ioc_subset_Ioi_self

/-- **Stone 7' (key)**: `∑_{m<N} e^{-b(m+1)²} ≤ √(π/b)/2` for `b > 0`. -/
theorem sum_exp_neg_sq_le_gaussian (b : ℝ) (hb : 0 < b) :
    ∑ m : Fin N, Real.exp (-b * ((m : ℝ) + 1) ^ 2) ≤ Real.sqrt (Real.pi / b) / 2 := by
  have key := AntitoneOn.sum_le_integral (f := fun x : ℝ => Real.exp (-b * x ^ 2))
      (x₀ := (0:ℝ)) (a := N)
      (antitoneOn_gaussian b (le_of_lt hb) 0 (N:ℝ) le_rfl)
  refine le_trans ?_ (le_trans key (integral_zero_N_gaussian_le b hb))
  apply le_of_eq
  rw [Fin.sum_univ_eq_sum_range (fun i => Real.exp (-b * ((i : ℝ) + 1) ^ 2))]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring_nf

#print axioms sum_exp_neg_sq_le_gaussian

/-- **Stone 7' applied to heatWeight**: `∑_n e^{-s·λ_n} ≤ √(π/(s(π/L)²))/2` for `s>0`,
the sharp `s^{-1/2}` heat-sum bound in terms of the Galerkin eigenvalues. -/
theorem sum_heatWeight_le_sqrt (L : ℝ) (hL : 0 < L) (s : ℝ) (hs : 0 < s) :
    ∑ m : Fin N, heatWeight L s m ≤ Real.sqrt (Real.pi / (s * (Real.pi / L) ^ 2)) / 2 := by
  have hb : 0 < s * (Real.pi / L) ^ 2 := by positivity
  have hrw : ∀ m : Fin N, heatWeight L s m
      = Real.exp (-(s * (Real.pi / L) ^ 2) * ((m : ℝ) + 1) ^ 2) := by
    intro m
    unfold heatWeight galerkinLam
    congr 1
    ring
  simp only [hrw]
  exact sum_exp_neg_sq_le_gaussian (s * (Real.pi / L) ^ 2) hb

#print axioms sum_heatWeight_le_sqrt
end
end RHFormalization
