-- SENTINEL: matched-weighted-interacting-gain-v1
import RHFormalization.MatchedWeightedFreeResponseBridge
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module
open scoped BigOperators Classical

variable {N : ℕ}

/--
Fully interacting response of one unweighted singleton channel, evaluated
at the canonical spectral shift `s + 1/4`.
-/
def matchedPairPerturbedResponse
    (μ : Fin N → ℝ)
    (q : PrimePowerPair) (L : ℝ) (s : ℂ) : ℂ :=
  LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
    (Matrix.toEuclideanLin
        (galerkinTC (N := N) L q.center)
      *
     perturbedResolventOp μ
       (matchedUnitChannelVC_isHermitian
         (N := N) q L)
       (s + (1 / 4 : ℂ)))

/--
The actual gain supplied by switching one channel from the free resolvent
to the fully interacting singleton resolvent.
-/
def matchedPairInteractingGain
    (μ : Fin N → ℝ)
    (q : PrimePowerPair) (L : ℝ) (s : ℂ) : ℂ :=
  matchedPairPerturbedResponse
      (N := N) μ q L s
    -
  matchedPairFreeResponse
      (N := N) μ q L s

/--
Density-normalized weighted sum of the fully interacting singleton
responses at the live adaptive schedule.

The frozen arithmetic weight occurs once, outside each independent
unit-potential channel.
-/
def matchedAdaptiveWeightedPerturbedResponse
    (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
    ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
      q.weightC *
        matchedPairPerturbedResponse
          (N := adaptiveN c n)
          (fun m =>
            galerkinLam (adaptiveL c n) (m : ℕ))
          q (adaptiveL c n) s

/--
Density-normalized weighted sum of the singleton interacting gains.
-/
def matchedAdaptiveWeightedInteractingGain
    (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
    ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
      q.weightC *
        matchedPairInteractingGain
          (N := adaptiveN c n)
          (fun m =>
            galerkinLam (adaptiveL c n) (m : ℕ))
          q (adaptiveL c n) s

/--
Exact separation of the matched interacting response into the already
banked weighted free response plus the genuinely new interacting gain.
-/
theorem matchedAdaptiveWeightedPerturbedResponse_eq_free_add_gain
    (c : ℝ) (n : ℕ) (s : ℂ) :
    matchedAdaptiveWeightedPerturbedResponse c n s
      =
    matchedAdaptiveWeightedFreeResponse c n s
      +
    matchedAdaptiveWeightedInteractingGain c n s := by
  unfold matchedAdaptiveWeightedPerturbedResponse
    matchedAdaptiveWeightedFreeResponse
    matchedAdaptiveWeightedInteractingGain
    matchedPairInteractingGain

  calc
    (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
        ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            matchedPairPerturbedResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s
      =
    (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
        ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          (q.weightC *
            matchedPairFreeResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s
          +
          q.weightC *
            (matchedPairPerturbedResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s
            -
            matchedPairFreeResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro q _hq
        ring
    _ =
      (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
        (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            matchedPairFreeResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s
        +
        ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            (matchedPairPerturbedResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s
            -
            matchedPairFreeResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s)) := by
        rw [Finset.sum_add_distrib]
    _ =
      (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
        ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            matchedPairFreeResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s
      +
      (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
        ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            (matchedPairPerturbedResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s
            -
            matchedPairFreeResponse
              (N := adaptiveN c n)
              (fun m =>
                galerkinLam (adaptiveL c n) (m : ℕ))
              q (adaptiveL c n) s) := by
        ring

/--
The canonical route lock rewritten so that the new interacting gain is
visible explicitly.

This theorem identifies exactly where any new cancellation must occur.
-/
theorem matchedAdaptiveWeightedPerturbed_sub_gain_route_lock
    (c : ℝ) (n : ℕ) (s : ℂ) :
    matchedAdaptiveWeightedPerturbedResponse c n s
      -
    matchedAdaptiveWeightedInteractingGain c n s
      =
    (1 / 2 : ℂ) *
        galerkinStagePackage.B_stage
          (adaptiveGalerkinStageSeq c n) s
      - adaptiveBcorrWin c n s
      + adaptiveGalerkinTransformDefect c n s := by
  rw [matchedAdaptiveWeightedPerturbedResponse_eq_free_add_gain]
  rw [matchedAdaptiveWeightedFreeResponse_route_lock]
  ring

#print axioms matchedPairPerturbedResponse
#print axioms matchedPairInteractingGain
#print axioms matchedAdaptiveWeightedPerturbedResponse
#print axioms matchedAdaptiveWeightedInteractingGain
#print axioms matchedAdaptiveWeightedPerturbedResponse_eq_free_add_gain
#print axioms matchedAdaptiveWeightedPerturbed_sub_gain_route_lock

end

end RHFormalization
