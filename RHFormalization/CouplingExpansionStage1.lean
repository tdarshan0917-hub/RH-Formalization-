-- SENTINEL: coupling-expansion-s1-v1
import RHFormalization.CouplingDerivativeIdentity
import RHFormalization.AdmissiblePrimeStageIdentity
import Mathlib

/-!
# CouplingExpansionStage1 — exact paired second-resolvent expansion

Stage 1 of the CHANNELWISE COUPLING DERIVATIVE.  Exact algebra only; no
limit, no derivative, no bound.

  `Tr(T·R_λ) - Tr(T·R_0) = -Tr(T·R_0·V·R_0) + Tr(T·R_0·V·R_λ·V·R_0)`

where `R_0 = freeResolventOpE μ w` and `R_λ = perturbedResolventOp μ hV w`.
Taking `T = galerkinTC L (log q)` and `V` a single prime well gives GPT's
channelwise object with ONE arithmetic weight and NO mixed channels.

Stage 2 (separate file) supplies `d/dλ|_{λ=0}` from this, and needs
resolvent-norm continuity in λ.

ROUTE CARD
1. Consumes the banked `resolvent_sub_eq_first_plus_second`.
2. Raw B on Ω? NO. B−M as a Prop? NO. No bound asserted.
3. Consumer: Stage 2 (coupling derivative), then the response identity.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module
open scoped BigOperators

variable {N : ℕ}

/-- **Paired second-resolvent expansion, exact.**  The paired resolvent
difference splits into the first-order (Born) term plus the second-order
remainder, with an arbitrary observable `T` in the trace slot. -/
theorem paired_resolvent_sub_eq_first_plus_second
    (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) (w : ℂ)
    (hneF : ∀ i, w + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ i, w + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (Matrix.toEuclideanLin T * perturbedResolventOp μ hV w)
      - LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (Matrix.toEuclideanLin T * freeResolventOpE μ w)
      = -(LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
            (Matrix.toEuclideanLin T * freeResolventOpE μ w
              * Matrix.toEuclideanLin V * freeResolventOpE μ w))
        + LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
            (Matrix.toEuclideanLin T * freeResolventOpE μ w
              * Matrix.toEuclideanLin V * perturbedResolventOp μ hV w
              * Matrix.toEuclideanLin V * freeResolventOpE μ w) := by
  have hres := resolvent_sub_eq_first_plus_second μ hV w hneF hneP
  have hpre : Matrix.toEuclideanLin T
        * (perturbedResolventOp μ hV w - freeResolventOpE μ w)
      = Matrix.toEuclideanLin T * perturbedResolventOp μ hV w
        - Matrix.toEuclideanLin T * freeResolventOpE μ w := by
    first
      | rw [mul_sub]
      | (simp only [mul_sub])
      | ring
  have hstep : Matrix.toEuclideanLin T
        * (perturbedResolventOp μ hV w - freeResolventOpE μ w)
      = Matrix.toEuclideanLin T
          * (-(freeResolventOpE μ w * Matrix.toEuclideanLin V
                * freeResolventOpE μ w)
             + freeResolventOpE μ w * Matrix.toEuclideanLin V
                * perturbedResolventOp μ hV w * Matrix.toEuclideanLin V
                * freeResolventOpE μ w) := by
    rw [hres]
  rw [hpre] at hstep
  have hmap := congrArg
    (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))) hstep
  rw [map_sub] at hmap
  simpa only [mul_add, mul_neg, map_add, map_neg, mul_assoc] using hmap

#print axioms paired_resolvent_sub_eq_first_plus_second

end

end RHFormalization
