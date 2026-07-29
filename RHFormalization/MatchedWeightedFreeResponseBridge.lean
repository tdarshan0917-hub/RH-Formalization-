-- SENTINEL: matched-weighted-free-response-bridge-v1
import RHFormalization.DecodedGalerkinFStageForwardGate
import RHFormalization.GalerkinCanonicalFSlot
import RHFormalization.FreePairedTraceIdentity
import RHFormalization.AdaptiveGalerkinDefectGate
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module
open scoped BigOperators Classical

variable {N : ℕ}

/--
One unweighted physical singleton bump.

The arithmetic weight is deliberately NOT inside this potential. It will
multiply the entire channel response externally, exactly once.
-/
def matchedUnitChannelVC
    (q : PrimePowerPair) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  decodedGalerkinVC
    (N := N) 1 {ppCode q}
    (fun _ : ℕ => (1 : ℝ)) L

/-- The unweighted singleton channel is Hermitian. -/
theorem matchedUnitChannelVC_isHermitian
    (q : PrimePowerPair) (L : ℝ) :
    (matchedUnitChannelVC (N := N) q L).IsHermitian := by
  exact decodedGalerkinVC_isHermitian
    (N := N) 1 {ppCode q}
    (fun _ : ℕ => (1 : ℝ)) L

/--
Free response of one channel at the canonical spectral shift `s + 1/4`.

No arithmetic weight occurs in this definition.
-/
def matchedPairFreeResponse
    (μ : Fin N → ℝ)
    (q : PrimePowerPair) (L : ℝ) (s : ℂ) : ℂ :=
  LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
    (Matrix.toEuclideanLin
        (galerkinTC (N := N) L q.center)
      *
     freeResolventOpE μ (s + (1 / 4 : ℂ)))

/--
The channel free response is exactly the banked finite spike transform.

This is the decisive canonical-contact identity.
-/
theorem matchedPairFreeResponse_eq_spikeTransform
    (μ : Fin N → ℝ)
    (q : PrimePowerPair) (L : ℝ) (s : ℂ) :
    matchedPairFreeResponse (N := N) μ q L s
      =
    galerkinSpikeTransform (N := N) μ L q.center s := by
  unfold matchedPairFreeResponse
  rw [LinearMap.trace_mul_comm]
  simpa [galerkinTC] using
    (galerkinSpikeTransform_eq_trace
      (N := N) μ L q.center s).symm

/--
The adaptive weighted free response.

The arithmetic weight is outside each independent channel and therefore
appears exactly once. There is no globally weighted potential and no
mixed-channel expansion.
-/
def matchedAdaptiveWeightedFreeResponse
    (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) *
    ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
      q.weightC *
        matchedPairFreeResponse
          (N := adaptiveN c n)
          (fun m =>
            galerkinLam (adaptiveL c n) (m : ℕ))
          q (adaptiveL c n) s

/--
Exact identification with the already-banked adaptive free paired
transform.
-/
theorem matchedAdaptiveWeightedFreeResponse_eq_freePaired
    (c : ℝ) (n : ℕ) (s : ℂ) :
    matchedAdaptiveWeightedFreeResponse c n s
      =
    adaptiveFreePairedTransform c n s := by
  unfold matchedAdaptiveWeightedFreeResponse
    adaptiveFreePairedTransform
    decodedOneLetterTransform

  apply congrArg
    (fun X : ℂ =>
      (((1 / (2 * adaptiveL c n) : ℝ) : ℂ)) * X)

  refine Finset.sum_congr rfl ?_
  intro q _hq
  rw [matchedPairFreeResponse_eq_spikeTransform]

/--
The matched weighted free response therefore has the literal canonical
route lock:

  weighted free response
    = 1/2 B_stage - window correction + Galerkin defect.
-/
theorem matchedAdaptiveWeightedFreeResponse_route_lock
    (c : ℝ) (n : ℕ) (s : ℂ) :
    matchedAdaptiveWeightedFreeResponse c n s
      =
    (1 / 2 : ℂ) *
        galerkinStagePackage.B_stage
          (adaptiveGalerkinStageSeq c n) s
      - adaptiveBcorrWin c n s
      + adaptiveGalerkinTransformDefect c n s := by
  rw [matchedAdaptiveWeightedFreeResponse_eq_freePaired]
  exact adaptiveFreePairedTransform_route_lock c n s

#print axioms matchedUnitChannelVC
#print axioms matchedUnitChannelVC_isHermitian
#print axioms matchedPairFreeResponse
#print axioms matchedPairFreeResponse_eq_spikeTransform
#print axioms matchedAdaptiveWeightedFreeResponse
#print axioms matchedAdaptiveWeightedFreeResponse_eq_freePaired
#print axioms matchedAdaptiveWeightedFreeResponse_route_lock

end

end RHFormalization
