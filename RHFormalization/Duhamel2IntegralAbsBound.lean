import RHFormalization.Duhamel2IntegratedBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/--
The integral of the absolute value of the all-free order-2 Duhamel
integrand is bounded independently of the Galerkin dimension `N`
and independently of the heat time `t`.

This is stronger than the triangle-bound conclusion
`abs_duhamel2Term_le_const` and is consumed by the shifted
all-free contribution to the exact order-2 sandwich remainder.
-/
theorem integral_abs_duhamel2Integrand_le_const
    (δ : ℝ) (hδ : 0 < δ)
    (qs : Finset ℕ) (w : ℕ → ℝ)
    (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) :
    (∫ u in (0 : ℝ)..t,
        |duhamel2Integrand (N := N) δ qs w L t u|)
      ≤
    ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
      * (L ^ 2 / Real.pi) := by

  set B :=
    ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L)
      with hB

  set C :=
    (L / (2 * Real.sqrt Real.pi)) ^ 2
      with hC

  have hpt :
      ∀ u ∈ Set.Ioo (0 : ℝ) t,
        |duhamel2Integrand (N := N) δ qs w L t u|
          ≤
        B ^ 2 * C *
          ((t - u) ^ (-(1 : ℝ) / 2)
            * u ^ (-(1 : ℝ) / 2)) := by
    intro u hu
    obtain ⟨hu0, hut⟩ := hu

    have htu : 0 < t - u := by
      linarith

    refine le_trans
      (abs_duhamel2Integrand_le_sqrt
        (N := N)
        δ hδ qs w L hL
        t u hu0 htu) ?_

    rw [sqrt_heat_factor L (t - u) hL htu,
        sqrt_heat_factor L u hL hu0,
        hC]

    apply le_of_eq
    ring

  -- Keep the dot-method applications on named hypotheses so the parser
  -- cannot treat a leading dot on a new line as an extra argument.
  have hcont_abs :
      Continuous
        (fun u : ℝ =>
          |duhamel2Integrand (N := N) δ qs w L t u|) := by
    exact (duhamel2Integrand_continuous
      (N := N) δ qs w L t).abs

  have hint_lhs :
      IntervalIntegrable
        (fun u : ℝ =>
          |duhamel2Integrand (N := N) δ qs w L t u|)
        MeasureTheory.volume 0 t := by
    exact hcont_abs.intervalIntegrable 0 t

  have hbeta :
      IntervalIntegrable
        (fun u : ℝ =>
          (t - u) ^ (-(1 : ℝ) / 2)
            * u ^ (-(1 : ℝ) / 2))
        MeasureTheory.volume 0 t := by
    exact intervalIntegrable_beta_integrand t ht

  have hint_rhs :
      IntervalIntegrable
        (fun u : ℝ =>
          B ^ 2 * C *
            ((t - u) ^ (-(1 : ℝ) / 2)
              * u ^ (-(1 : ℝ) / 2)))
        MeasureTheory.volume 0 t := by
    exact hbeta.const_mul (B ^ 2 * C)

  calc
    (∫ u in (0 : ℝ)..t,
        |duhamel2Integrand (N := N) δ qs w L t u|)
        ≤
      ∫ u in (0 : ℝ)..t,
        B ^ 2 * C *
          ((t - u) ^ (-(1 : ℝ) / 2)
            * u ^ (-(1 : ℝ) / 2)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo
        ht.le hint_lhs hint_rhs hpt

    _ =
      B ^ 2 * C *
        ∫ u in (0 : ℝ)..t,
          ((t - u) ^ (-(1 : ℝ) / 2)
            * u ^ (-(1 : ℝ) / 2)) := by
      rw [intervalIntegral.integral_const_mul]

    _ ≤ B ^ 2 * C * 4 := by
      apply mul_le_mul_of_nonneg_left
        (beta_conv_bound t ht)
      rw [hC]
      positivity

    _ = B ^ 2 * (L ^ 2 / Real.pi) := by
      rw [hC,
        show
          (L / (2 * Real.sqrt Real.pi)) ^ 2
            = L ^ 2 / (4 * Real.pi) by
          rw [div_pow, mul_pow,
              Real.sq_sqrt Real.pi_pos.le]
          ring]
      ring

#print axioms integral_abs_duhamel2Integrand_le_const

end

end RHFormalization
