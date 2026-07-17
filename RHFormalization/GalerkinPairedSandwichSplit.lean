import RHFormalization.GalerkinFullToDiagonalDuhamelSplit
import RHFormalization.GalerkinDuhamel1Term
import RHFormalization.GalerkinSpikeComplexify
import Mathlib

/-!
# Paired sandwich split — FRONTIER BRICK F1 (ONE-STEP′′ opening)
SENTINEL: paired-sandwich-split-v1

ROUTE CARD
1. `pairedDuhamel1Integrand`: the T_a-paired order-1 Duhamel integrand
   `Tr(D(t−u)·V·D_exp(u)·T_a)` — the object whose spike sum produces the
   arithmetic one-letter package (the P^can of ONE-STEP′′).
2. `galerkinPairedSandwich_trace_split`: the paired Duhamel integrand
   splits into (−pairedDuhamel1) + paired quadratic remainder — by
   `congrArg (· * T_a)` on the BANKED operator split + trace_add.
3. This is the exact decomposition the ONE-STEP′′ word sorting refines:
   order-1 → spike/error (paired analogues of the banked bounds);
   quadratic → the D.ADM-anchored remainder estimate.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- **Paired order-1 Duhamel integrand**: `Tr(D(t−u)·V·D_exp(u)·T_a)`. The
displacement-paired analogue of the banked `duhamel1Integrand`. -/
noncomputable def pairedDuhamel1Integrand
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u a : ℝ) : ℝ :=
  (Matrix.diagonal (heatWeight (N := N) L (t - u))
    * galerkinV (N := N) δ qs w L
    * NormedSpace.exp (u • (-(galerkinK (N := N) L)))
    * galerkinT (N := N) L a).trace

/-- **F1 — the paired trace split.** The paired Duhamel integrand splits into
the (negated) paired order-1 term plus the paired quadratic remainder. -/
theorem galerkinPairedSandwich_trace_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u a : ℝ) :
    (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))
        * galerkinT (N := N) L a).trace
      = - pairedDuhamel1Integrand (N := N) δ qs w L t u a
        + (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
            * (-(galerkinV (N := N) δ qs w L))
            * (∫ s in (0:ℝ)..u,
                NormedSpace.exp ((u - s) • (-(galerkinK (N := N) L)))
                  * (-(galerkinV (N := N) δ qs w L))
                  * NormedSpace.exp (s • (-(galerkinK (N := N) L
                      + galerkinV (N := N) δ qs w L))))
            * galerkinT (N := N) L a).trace := by
  set T : Matrix (Fin N) (Fin N) ℝ := galerkinT (N := N) L a with hT
  have hsplit := galerkinFullSandwich_split (N := N) δ qs w L t u
  have hmul := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M * T) hsplit
  simp only [add_mul] at hmul
  have htr := congrArg Matrix.trace hmul
  rw [Matrix.trace_add] at htr
  rw [htr]
  congr 1
  -- first term: D·(−V)·D_exp·T = −(D·V·D_exp·T), trace_neg
  unfold pairedDuhamel1Integrand
  rw [hT]
  first
    | (rw [mul_neg, neg_mul, neg_mul, Matrix.trace_neg])
    | (rw [mul_neg, neg_mul, Matrix.trace_neg])
    | (simp only [mul_neg, neg_mul, Matrix.trace_neg])
    | (rw [show Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
          * (-(galerkinV (N := N) δ qs w L))
          * NormedSpace.exp (u • (-(galerkinK (N := N) L)))
          * galerkinT (N := N) L a
        = -(Matrix.diagonal (heatWeight (N := N) L (t - u))
          * galerkinV (N := N) δ qs w L
          * NormedSpace.exp (u • (-(galerkinK (N := N) L)))
          * galerkinT (N := N) L a) by ring]
       rw [Matrix.trace_neg])

#print axioms pairedDuhamel1Integrand
#print axioms galerkinPairedSandwich_trace_split

end

end RHFormalization
