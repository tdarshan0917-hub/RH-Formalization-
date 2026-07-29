-- SENTINEL: SEAMRED-v1
import RHFormalization.B2OneLetterConnector
import RHFormalization.DecodedCanonicalSectorDecomposition
import Mathlib

/-!
# SeamArithmeticReduction — what the seam actually equals

From the banked one-letter identity
  B_stage = 2·FreePaired − 2·defect + windowCorr
and the definition
  decodedBulkSeam = 2·FreePaired − compensatorM,
pure algebra gives

  decodedBulkSeam = (B_stage − compensatorM) + 2·defect − windowCorr.

CONSEQUENCE (stated, not assumed): since `defect` and `windowCorr` are both
banked-bounded on Ω-compacts, the seam is bounded IFF `B_stage − compensatorM`
is bounded. This makes the character of the frontier a kernel fact rather
than an assertion.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **THE SEAM REDUCTION** — pure algebra over the banked one-letter identity. -/
theorem decodedBulkSeam_eq_compensatedB_add_corrections (c : ℝ) (n : ℕ) (s : ℂ) :
    decodedBulkSeam c n s
      = (galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
          - compensatorM n s)
        + 2 * adaptiveGalerkinTransformDefect c n s
        - decodedWindowCorrection c n s := by
  have hB := adaptive_B_stage_eq_oneLetter c n s
  unfold decodedBulkSeam
  rw [hB]
  ring

#print axioms decodedBulkSeam_eq_compensatedB_add_corrections

end

end RHFormalization
