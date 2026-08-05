import RHFormalization.GreenSqDiagonalClosed
import Mathlib

/-!
# GreenSqHalfLineTarget — P2-C1: the continuum target and the exact remainder

ROUTE CARD
1. Target: (i) define the half-line squared-resolvent diagonal
   `greenSqHalfLine κ a := (1 − e^{−2κa}(1+2κa))/(4κ³)` — symbolically
   triple-verified as the L→∞ limit of the banked closed form AND the
   direct half-line integral ∫₀^∞ G∞(x,a)² dx; (ii) define the exact
   remainder `greenSqRemainder := (closed form) − greenSqHalfLine`;
   (iii) prove `∫₀^L G² = greenSqHalfLine + greenSqRemainder` (exact, by
   the banked P2-B2 identity + defn). The remainder BOUND
   `|rem| ≤ (L/κ²)e^{−2κ(L−a)}` (numerically verified, ratio<0.5) is P2-C2.
2. Raw B on Ω? NO. B−M bare Prop? NO — definitions + banked identity.
3. Consumer: P2-C2 (remainder bound along schedule) + the mode-sum
   identification (P2-B3) → combined-profile continuum match (go/no-go).
-/

set_option autoImplicit false

namespace RHFormalization

open Real

/-- **The continuum target**: half-line squared-resolvent diagonal at
center `a`: `∫₀^∞ ((e^{−κ|x−a|} − e^{−κ(x+a)})/(2κ))² dx`. -/
noncomputable def greenSqHalfLine (κ a : ℝ) : ℝ :=
  (1 - Real.exp (-(2 * κ * a)) * (1 + 2 * κ * a)) / (4 * κ^3)

/-- **The exact finite-box remainder** (definitionally the difference). -/
noncomputable def greenSqRemainder (κ L a : ℝ) : ℝ :=
  (Real.sinh (κ * (L - a)) ^ 2
        * (Real.sinh (κ * a) * Real.cosh (κ * a) / κ - a)
      + Real.sinh (κ * a) ^ 2
        * (Real.sinh (κ * (L - a)) * Real.cosh (κ * (L - a)) / κ
            - (L - a)))
    / (2 * (κ * Real.sinh (κ * L)) ^ 2)
  - greenSqHalfLine κ a

/-- **P2-C1: the exact continuum split of the squared-Green diagonal.** -/
theorem greenSq_diagonal_eq_halfLine_add_remainder (κ L a : ℝ)
    (hκ : 0 < κ) (hL : 0 < L) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    (∫ x in (0:ℝ)..L, dirichletGreen L κ x a ^ 2)
      = greenSqHalfLine κ a + greenSqRemainder κ L a := by
  rw [greenSq_diagonal_closed κ L a hκ hL ha0 haL]
  unfold greenSqRemainder
  ring

#print axioms greenSqHalfLine
#print axioms greenSqRemainder
#print axioms greenSq_diagonal_eq_halfLine_add_remainder

end RHFormalization
