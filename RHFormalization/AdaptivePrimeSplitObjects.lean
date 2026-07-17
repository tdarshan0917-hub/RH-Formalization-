import RHFormalization.AdaptiveFreeSplit
import RHFormalization.AdmissiblePrimeFirstOrderSplit
import Mathlib

/-!
# AdaptivePrimeSplitObjects — the adaptive resolvent split objects

Mirrors `FirstOrderWindow` / `SecondResolventResidual` at the adaptive
parameters `(adaptiveN c n, adaptiveL c n, adaptiveDensityC c n)`; cutoff
and weights unchanged. These are the exact bookkeeping objects for the
adaptive FMR bridge.

Analytic roles (per the hybrid design):
- `adaptiveFirstOrderWindow` → one-letter/window estimate (separate);
- `adaptiveSecondResolventResidual` = (1/2L)·Tr(R_D V R_H V R_D) with the
  FULL perturbed resolvent R_H — contains the complete all-orders tail —
  to be bounded via the manuscript D.LOC chain consuming
  `adaptiveGalerkinStage_DADM`. The old cubic-net `C/(n+2)` estimates are
  NOT inherited.

The exact identity `adaptiveFadmPrimeStage = first + second` is the next
brick (mirror of `FadmPrimeStage_eq_first_plus_second`).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- **Adaptive first-order window** (sign carried in the definition):
`−adaptiveDensityC·Tr(R_D V R_D)` at `s + SupVConst`. -/
def adaptiveFirstOrderWindow (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  -(adaptiveDensityC c n *
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (adaptiveN c n)))
      (freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
          (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (galerkinVC (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
        * freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
            (s + (SupVConst : ℂ))))

/-- **Adaptive second-resolvent residual** (combined, positive orientation):
`+adaptiveDensityC·Tr(R_D V R_H V R_D)` at `s + SupVConst`, with the full
perturbed resolvent `R_H` — the complete all-orders tail. -/
def adaptiveSecondResolventResidual (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  adaptiveDensityC c n *
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (adaptiveN c n)))
      (freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
          (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (galerkinVC (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
        * perturbedResolventOp (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
            (galerkinVC_isHermitian (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
            (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (galerkinVC (N := adaptiveN c n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
              (adaptiveL c n))
        * freeResolventOpE (galerkinFreeMu (adaptiveN c n) (adaptiveL c n))
            (s + (SupVConst : ℂ)))

/-- The adaptive O2-shaped short residual (assembled by triangle inequality
once the two analytic providers land). -/
def adaptiveShortResidual (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  adaptiveFirstOrderWindow c n s + adaptiveSecondResolventResidual c n s

#print axioms adaptiveFirstOrderWindow
#print axioms adaptiveSecondResolventResidual
#print axioms adaptiveShortResidual

end

end RHFormalization
