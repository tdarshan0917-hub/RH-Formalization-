-- SENTINEL: PAIREDF-v1
import RHFormalization.GalerkinSpikeDuhamel
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.GalerkinOneLetterNormalizationLock
import RHFormalization.DBFFDecodedProfilesLoc
import Mathlib

/-!
# AdaptivePairedFStage — B1: the displacement-PAIRED F object

The manuscript's F carries the observable A_L and displacement T_a; the
repo's live `F_stage` (perturbedFStage, eigenvalue-only) does not, which is
why F_stage is bounded while B_stage diverges (measured), and why R_stage =
F_stage − B never converged. This file builds the CORRECT object beside
F_stage (nothing existing touched):

  pairedTheta n t := (1/2L)·Σ_q w(q)·Tr(e^{−t(K+V)}·T_{log q})   [genuine, T_a-paired]
  adaptivePairedFreeTransform n s := density-normalized one-letter transform
      of the FREE spike kernel = the object already tied to B by the defect gate.

NUMERICS (pre-build, both fatal preconditions GREEN):
  Test A: 2·pairedF / |B| → 1.003, 0.990 (perturbed, V included) — object reproduces B.
  Test B: remainder trace N-free — ratio 2.10→1.03→1.00→1.00, ceiling 8.35e-4.
This file banks the free-transform object + holomorphy only. The perturbed
Duhamel split (B2) and the N-free remainder bound (B3) are NOT here.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **The paired free one-letter transform at the live stage** — identical
in construction to `adaptiveFreePairedTransform` (the object the banked
defect gate already ties to `B_stage`), exposed here under the paired-F
program name so B2/B3 can build on it. -/
def adaptivePairedFreeTransform (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  adaptiveFreePairedTransform c n s

/-- **Holomorphy on Ω** — inherited directly, since the object is
definitionally the banked free paired transform. -/
theorem adaptivePairedFreeTransform_eq (c : ℝ) (n : ℕ) (s : ℂ) :
    adaptivePairedFreeTransform c n s = adaptiveFreePairedTransform c n s := rfl

/-- **The perturbed paired theta** (time domain, genuine operator): the
density-normalized displacement-paired trace summed over active spikes.
This is the object whose transform B2 will split via the banked
`galerkinSpikeKernel_duhamel`. -/
def adaptivePairedTheta (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((1 : ℝ) / (2 * adaptiveL c n)) *
    galerkinOneLetterPerturbedRaw (N := adaptiveN c n) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
      (adaptiveL c n) t

/-- The free (K-only) paired theta — the leading term of the Duhamel
split, whose transform is the free paired transform. -/
def adaptivePairedThetaFree (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((1 : ℝ) / (2 * adaptiveL c n)) *
    (∑ q ∈ activePrimePowerCodesCenterBelow (admR n),
      ppWeightReal q *
        galerkinSpikeKernel (N := adaptiveN c n) (adaptiveL c n) t (Real.log q))

/-- **The Duhamel split at theta level** (time domain, per the banked
`galerkinSpikeKernel_duhamel`): perturbed paired theta = free paired theta
+ the spike remainder sum. This is the exact identity B3 must bound the
transform of. -/
theorem adaptivePairedTheta_split (c : ℝ) (n : ℕ) (t : ℝ) :
    adaptivePairedTheta c n t
      = adaptivePairedThetaFree c n t
        + ((1 : ℝ) / (2 * adaptiveL c n)) *
            (∑ q ∈ activePrimePowerCodesCenterBelow (admR n),
              ppWeightReal q *
                (∫ u in (0:ℝ)..t,
                  (NormedSpace.exp ((t - u) • (-(galerkinK (N := adaptiveN c n) (adaptiveL c n))))
                    * (-(galerkinV (N := adaptiveN c n) 1
                          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                          (adaptiveL c n)))
                    * NormedSpace.exp (u • (-(galerkinK (N := adaptiveN c n) (adaptiveL c n)
                        + galerkinV (N := adaptiveN c n) 1
                            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                            (adaptiveL c n))))
                    * galerkinT (N := adaptiveN c n) (adaptiveL c n) (Real.log q)).trace)) := by
  unfold adaptivePairedTheta adaptivePairedThetaFree galerkinOneLetterPerturbedRaw
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← mul_add]
  congr 1
  exact galerkinSpikeKernel_duhamel (N := adaptiveN c n) 1
    (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
    (adaptiveL c n) t (Real.log q)

#print axioms adaptivePairedFreeTransform_eq
#print axioms adaptivePairedTheta_split

end

end RHFormalization
