-- SENTINEL: quad-integrand-frob-bound-v1
import RHFormalization.QuadRemainderSandwichNormSplit
import RHFormalization.FrobContractionSandwich
import RHFormalization.AdmissibleWeightNonneg
import Mathlib

/-!
# N-free pointwise bound for the quadratic Duhamel integrand

Composition of banked bricks: trace Cauchy–Schwarz (`abs_trace_mul_le_frob`)
+ the N-free sandwich (`frobSq_sandwich_le`) + the stage form floor
(`galerkinV_form_nonneg_L`). Result: the s-integrand of the quadratic
remainder is bounded by `√frobSq(D·V) · √frobSq(V)` — s-free and N-free.
DOWNSTREAM CONSUMER: quadRemainder_trace_le_integral_abs RHS → short-time
sector local boundedness along α → h_conv.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Frobenius square ignores sign. -/
theorem frobSq_neg (A : Matrix (Fin N) (Fin N) ℝ) :
    frobSq (-A) = frobSq A := by
  unfold frobSq
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.neg_apply, neg_sq]

/-- **The N-free, s-free integrand bound at the stage parameters.**
Exact integrand of `quadRemainder_trace_le_integral_abs`; simplex
constraints `0 ≤ s`, `s ≤ u` only. -/
theorem quadIntegrand_trace_frob_le
    (qs : Finset ℕ) (L : ℝ) (hL : 0 < L) (hN : 0 < N)
    (t u s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    |((Matrix.diagonal fun m => heatWeight L (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal L))
        * (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
            * (-(galerkinV (N := N) 1 qs ppWeightReal L))
            * NormedSpace.exp (s • -(galerkinK (N := N) L
                + galerkinV (N := N) 1 qs ppWeightReal L)))).trace|
      ≤ Real.sqrt (frobSq
            ((Matrix.diagonal fun m => heatWeight L (t - u) m)
              * (-(galerkinV (N := N) 1 qs ppWeightReal L))))
        * Real.sqrt (frobSq (galerkinV (N := N) 1 qs ppWeightReal L)) := by
  have hV : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        v m * v n * galerkinV (N := N) 1 qs ppWeightReal L m n := by
    intro v
    first
      | exact galerkinV_form_nonneg_L L hL qs v
      | exact galerkinV_form_nonneg_L (N := N) L hL qs v
      | exact galerkinV_form_nonneg_L (L := L) hL qs v
  have hus : (0:ℝ) ≤ u - s := by linarith
  have hCS := abs_trace_mul_le_frob
    ((Matrix.diagonal fun m => heatWeight L (t - u) m)
      * (-(galerkinV (N := N) 1 qs ppWeightReal L)))
    (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
      * (-(galerkinV (N := N) 1 qs ppWeightReal L))
      * NormedSpace.exp (s • -(galerkinK (N := N) L
          + galerkinV (N := N) 1 qs ppWeightReal L)))
  have hsand := frobSq_sandwich_le 1 qs ppWeightReal L hN hV
    (-(galerkinV (N := N) 1 qs ppWeightReal L)) hus hs
  have hneg := frobSq_neg (galerkinV (N := N) 1 qs ppWeightReal L)
  refine le_trans hCS ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  calc frobSq (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
        * (-(galerkinV (N := N) 1 qs ppWeightReal L))
        * NormedSpace.exp (s • -(galerkinK (N := N) L
            + galerkinV (N := N) 1 qs ppWeightReal L)))
      ≤ frobSq (-(galerkinV (N := N) 1 qs ppWeightReal L)) := hsand
    _ = frobSq (galerkinV (N := N) 1 qs ppWeightReal L) := hneg

#print axioms frobSq_neg
#print axioms quadIntegrand_trace_frob_le

end

end RHFormalization
