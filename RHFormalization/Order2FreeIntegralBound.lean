import RHFormalization.Order2PointwiseFreeIdent
import RHFormalization.Duhamel2IntegralAbsBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/--
The integral of the absolute value of the free order-2 integrand
is bounded uniformly (dimension-free).
-/
theorem integral_abs_galerkinOrder2Pointwise_free_le_const
    (δ : ℝ) (hδ : 0 < δ)
    (qs : Finset ℕ) (w : ℕ → ℝ)
    (L : ℝ) (hL : 0 < L)
    (t u : ℝ)
    (ht : 0 < t)
    (hu : 0 < u)
    (hut : u ≤ t) :
    (∫ r in (0 : ℝ)..u,
        |(
          NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (r • (-(galerkinK (N := N) L)))
        ).trace|)
      ≤
    ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
      * (L ^ 2 / Real.pi) := by

  -- Step 1: rewrite to duhamel2Integrand
  simp_rw [galerkinOrder2Pointwise_free_eq_duhamel2Integrand]

  -- Step 2: shift variable
  have hshift :
      (∫ r in (0 : ℝ)..u,
          |duhamel2Integrand (N := N) δ qs w L t (r + (t - u))|)
        =
      ∫ s in (t - u)..t,
          |duhamel2Integrand (N := N) δ qs w L t s| := by
    have hraw :=
      intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ))
        (b := u)
        (fun s : ℝ =>
          |duhamel2Integrand (N := N) δ qs w L t s|)
        (t - u)

    have hright : u + (t - u) = t := by
      ring

    simpa [hright] using hraw

  rw [hshift]

  -- Step 3: monotonicity to extend interval
  have hcont :
      Continuous fun s =>
        |duhamel2Integrand (N := N) δ qs w L t s| :=
    (duhamel2Integrand_continuous (N := N) δ qs w L t).abs

  have hint :
      IntervalIntegrable
        (fun s =>
          |duhamel2Integrand (N := N) δ qs w L t s|)
        volume 0 t :=
    hcont.intervalIntegrable 0 t

  have hmono :
      ∫ s in (t - u)..t,
          |duhamel2Integrand (N := N) δ qs w L t s|
      ≤
      ∫ s in (0 : ℝ)..t,
          |duhamel2Integrand (N := N) δ qs w L t s| := by
    refine intervalIntegral.integral_mono_interval
      (by linarith) (by linarith) le_rfl ?_ hint
    exact Filter.Eventually.of_forall (fun s => abs_nonneg _)

  -- Step 4: apply full integral bound
  exact
    hmono.trans
      (integral_abs_duhamel2Integrand_le_const
        (N := N) δ hδ qs w L hL t ht)

#print axioms integral_abs_galerkinOrder2Pointwise_free_le_const

end

end RHFormalization
