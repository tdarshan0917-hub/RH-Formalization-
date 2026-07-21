import RHFormalization.DecodedCanonicalSectorDecomposition
import RHFormalization.DBFFCompensator
import Mathlib

/-!
# SeamCoreForm — P2-4 target frozen

ROUTE CARD
1. Target: define `seamCore n = package − compensatorM` and prove the EXACT
   identity `decodedBulkSeam = 2·defect − windowCorrection + seamCore`.
   Pure algebra over banked identities; no bounds asserted.
2. Raw B on Ω? NO. B−M as bare Prop? NO — seamCore is controlled ONLY via
   P2-4/P2-5 (frozen rule 4).
3. Consumer: P2-4 (ε control via D.BFF expansion) → P2-5 → provider →
   RcanCandidate → HtailExists.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- **THE P2-4 OBJECT**: package-form B-side minus the main-term
compensator — all remaining analytic content of the live route. -/
def seamCore (n : ℕ) (s : ℂ) : ℂ :=
  finiteCanonicalPrimePowerPackage
      (activePrimePowerPairsCenterBelow (admR n))
      shiftedLaplaceHeatKernelC s
    - compensatorM n s

/-- **Exact seam localization.** -/
theorem decodedBulkSeam_eq_core_form (c : ℝ) (n : ℕ) (s : ℂ)
    (hL : adaptiveL c n ≠ 0) :
    decodedBulkSeam c n s
      = 2 * adaptiveGalerkinTransformDefect c n s
        - decodedWindowCorrection c n s
        + seamCore n s := by
  have hdef : adaptiveGalerkinTransformDefect c n s
      = adaptiveFreePairedTransform c n s
        - windowedCanonicalPackage
            (activePrimePowerPairsCenterBelow (admR n)) (adaptiveL c n)
            shiftedLaplaceHeatKernelC s := by
    first
      | rfl
      | (unfold adaptiveGalerkinTransformDefect; rfl)
  have hwin := package_sub_two_windowed_eq_correction c n s hL
  unfold decodedBulkSeam seamCore
  first
    | (rw [hdef, ← hwin]; ring)
    | linear_combination 2 * hdef - hwin
    | linear_combination 2 * hdef + hwin
    | linear_combination (-2 : ℂ) * hdef - hwin

#print axioms seamCore
#print axioms decodedBulkSeam_eq_core_form

end

end RHFormalization
