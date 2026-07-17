import RHFormalization.GalerkinPairingBounds
import RHFormalization.GalerkinSpikeLaplaceBridge
import Mathlib

/-!
# Adaptive Galerkin defect gate — G1 (objects + exact banked expression)
SENTINEL: defect-gate-g1-v1

ROUTE CARD
1. THE GO/NO-GO GATE (reprioritized ahead of the word tower): does the
   density-normalized decoded FREE paired transform converge to the windowed
   arithmetic package compact-uniformly on Ω? This file defines the exact
   objects; G2 (spectral truncation, L/N rate via the banked anchor) and
   G3 (Dirichlet-image vs Gaussian window — genuinely new content, reuse
   audit found only the arithmetic-side exhaustion tower) prove the decay;
   G4 assembles eps0.
2. NORMALIZATION SEAL: everything is expressed through the BANKED lock
   `adaptive_windowedCanonical_lock` — the proved `(1/2)·B_stage −
   adaptiveBcorrWin` with the factor 1/2 on the record, never guessed.
3. All pair-indexed, physical `q.center`, frozen `q.weightC`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- **The adaptive free paired transform**: density-normalized decoded free
spike transform at the live adaptive stage — the finite Galerkin object whose
convergence to the windowed package is the gate. -/
def adaptiveFreePairedTransform (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  decodedOneLetterTransform (N := adaptiveN c n)
    (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
    (activePrimePowerPairsCenterBelow (admR n))
    (adaptiveL c n) s

/-- **THE GATE OBJECT**: the adaptive Galerkin transform defect — free paired
transform minus the windowed canonical package (both at the live stage). -/
def adaptiveGalerkinTransformDefect (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  adaptiveFreePairedTransform c n s
    - windowedCanonicalPackage
        (activePrimePowerPairsCenterBelow (admR n)) (adaptiveL c n)
        shiftedLaplaceHeatKernelC s

/-- The defect is the banked per-stage defect object at the live parameters
(definitional cross-check against Brick 3a's `galerkinOneLetterDefect`). -/
theorem adaptiveGalerkinTransformDefect_eq_bankeDefect (c : ℝ) (n : ℕ) (s : ℂ) :
    adaptiveGalerkinTransformDefect c n s
      = galerkinOneLetterDefect (N := adaptiveN c n)
          (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
          (activePrimePowerPairsCenterBelow (admR n))
          (adaptiveL c n) shiftedLaplaceHeatKernelC s := rfl

/-- **THE NORMALIZATION SEAL**: through the banked adaptive lock, the free
transform = `(1/2)·B_stage(adaptive) − adaptiveBcorrWin + defect` — the
route-lock identity, exact, with the proved factor 1/2 on the record. -/
theorem adaptiveFreePairedTransform_route_lock (c : ℝ) (n : ℕ) (s : ℂ) :
    adaptiveFreePairedTransform c n s
      = (1 / 2 : ℂ) *
          galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
        - adaptiveBcorrWin c n s
        + adaptiveGalerkinTransformDefect c n s := by
  rw [← adaptive_windowedCanonical_lock c n s]
  unfold adaptiveGalerkinTransformDefect
  ring

/-- Per-spike defect (t-domain, real): finite-N density-normalized spike
kernel minus the Gaussian-window target — the object G2/G3 estimate. -/
def adaptiveSpikeDefectT (c : ℝ) (n : ℕ) (a t : ℝ) : ℝ :=
  (1 / (2 * adaptiveL c n)) *
      galerkinSpikeKernel (N := adaptiveN c n) (adaptiveL c n) t a
    - heatKernelRealScalar t a * ((adaptiveL c n - a) / (2 * adaptiveL c n))

/-- The stage mass: total active arithmetic weight (real parts of the frozen
weights) — the multiplier the G2/G3 rates must beat. -/
def adaptiveStageMass (n : ℕ) : ℝ :=
  ∑ q ∈ activePrimePowerPairsCenterBelow (admR n), ‖q.weightC‖

#print axioms adaptiveFreePairedTransform
#print axioms adaptiveGalerkinTransformDefect
#print axioms adaptiveGalerkinTransformDefect_eq_bankeDefect
#print axioms adaptiveFreePairedTransform_route_lock
#print axioms adaptiveSpikeDefectT
#print axioms adaptiveStageMass

end

end RHFormalization
