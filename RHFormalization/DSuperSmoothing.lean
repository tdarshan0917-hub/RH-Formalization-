import Mathlib
import RHFormalization.Basic

/-!
# RHFormalization.DSuperSmoothing

A theorem-facing predicate for Appendix-D mixed-word/super-smoothing control.

This does not prove the mixed-word estimates from operator theory.  It replaces
the remaining global axiom by an explicit quantitative certificate: the mixed-word
remainder has faster-than-polynomial decay in the summation index.
-/

namespace RHFormalization

noncomputable section

/--
A real sequence has super-polynomial decay if for every polynomial power `N`,
it is eventually bounded by a constant multiple of `(k+1)^{-N}`.

This is a concrete Lean-facing proxy for the Appendix-D mixed-word/super-smoothing
control certificate.
-/
def SuperPolynomialDecay
    (r : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ,
    0 ≤ C ∧
      ∀ k : ℕ,
        r k ≤ C / ((k + 1 : ℕ) : ℝ) ^ N

end

end RHFormalization
