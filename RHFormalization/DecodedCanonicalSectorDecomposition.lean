-- SENTINEL: decoded-canonical-sector-decomposition-v2
import RHFormalization.DecodedAdaptiveCombinedFreeR
import RHFormalization.DecodedAdaptivePrimeSplit
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.GalerkinOneLetterNormalizationLock
import Mathlib

/-!
# The exact decoded sector decomposition (and seam localization)

Four CONCRETE, independently defined objects:
* `decodedAdaptiveShortResidual` (banked; bounded by `decoded_hShort`),
* `adaptiveGalerkinTransformDefect` (banked; →0 by the eps0 gate),
* `decodedWindowCorrection` := (1/L)·Σ w(q)·a_q·K(a_q,s),
* `decodedBulkSeam` := 2·freePairedTransform − compensatorM.

Exact recombination (pure algebra over three banked identities):
  Combined = windowCorrection − 2·defect + bulkSeam − Short.
This localizes the entire open content of the hComb slot in
`decodedBulkSeam`, which visibly carries the arithmetic weights.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/-- **Window-correction sector** (concrete): the first-moment window error
of the one-letter extraction, `(1/L)·Σ w(q)·a_q·K(a_q,s)`. -/
def decodedWindowCorrection (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
    q.weightC * (((q.center / adaptiveL c n : ℝ)) : ℂ)
      * shiftedLaplaceHeatKernelC q.center s

/-- **Bulk seam** (concrete): twice the free paired transform minus the
compensator — the free-spectrum/classical-subtraction seam. -/
def decodedBulkSeam (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  2 * adaptiveFreePairedTransform c n s - compensatorM n s

/-- The window-factor identity at the package level:
`B − 2·W = windowCorrection`. -/
theorem package_sub_two_windowed_eq_correction (c : ℝ) (n : ℕ) (s : ℂ)
    (hL : adaptiveL c n ≠ 0) :
    finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow (admR n))
        shiftedLaplaceHeatKernelC s
      - 2 * windowedCanonicalPackage
          (activePrimePowerPairsCenterBelow (admR n)) (adaptiveL c n)
          shiftedLaplaceHeatKernelC s
      = decodedWindowCorrection c n s := by
  have hLC : ((adaptiveL c n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
  unfold finiteCanonicalPrimePowerPackage windowedCanonicalPackage
    decodedWindowCorrection
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [windowFactor_split (adaptiveL c n) q.center hL]
  have h2 : ((q.center / adaptiveL c n : ℝ) : ℂ)
      = 2 * ((q.center / (2 * adaptiveL c n) : ℝ) : ℂ) := by
    push_cast
    first
      | (field_simp)
      | (field_simp [hLC])
      | (rw [div_eq_div_iff hLC (by simpa using mul_ne_zero two_ne_zero hLC)]
         ring)
  rw [h2]
  ring

/-- **THE EXACT DECODED SECTOR DECOMPOSITION.** On Ω, the combined object
splits into the four concrete sectors. Pure algebra over the banked seal,
the banked prime split, the banked defect definition, and the
window-factor identity above. -/
theorem decodedAdaptiveCombinedFreeR_eq_sector_sum (c : ℝ) (n : ℕ)
    {s : ℂ} (hs : s ∈ Ω) (hL : adaptiveL c n ≠ 0) :
    decodedAdaptiveCombinedFreeR c n s
      = decodedWindowCorrection c n s
        - 2 * adaptiveGalerkinTransformDefect c n s
        + decodedBulkSeam c n s
        - decodedAdaptiveShortResidual c n s := by
  have hseal := decodedAdaptiveCombinedFreeR_eq c n s
  have hsplit := decodedFadmPrimeStage_eq_first_plus_second c n hs
  have hshort : decodedAdaptiveShortResidual c n s
      = decodedFadmPrimeStage c n s := by
    unfold decodedAdaptiveShortResidual
    rw [← hsplit]
  have hBform : DBFFO3CompensatedB n s
      = finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (admR n))
          shiftedLaplaceHeatKernelC s
        - compensatorM n s := by
    first
      | rfl
      | (unfold DBFFO3CompensatedB; rfl)
  have hwin := package_sub_two_windowed_eq_correction c n s hL
  have hdef : adaptiveGalerkinTransformDefect c n s
      = adaptiveFreePairedTransform c n s
        - windowedCanonicalPackage
            (activePrimePowerPairsCenterBelow (admR n)) (adaptiveL c n)
            shiftedLaplaceHeatKernelC s := by
    first
      | rfl
      | (unfold adaptiveGalerkinTransformDefect; rfl)
  rw [hseal, hshort]
  unfold decodedBulkSeam
  linear_combination hBform + hwin + 2 * hdef

#print axioms package_sub_two_windowed_eq_correction
#print axioms decodedAdaptiveCombinedFreeR_eq_sector_sum

end

end RHFormalization
