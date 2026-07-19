import RHFormalization.DBFFDecodedProfiles
import RHFormalization.DecodedCanonicalSectorDecomposition

/-!
# DBFFBulkSeamProfileForm — P2-3a: the bulk seam in profile vocabulary

ROUTE CARD
1. Target: the EXACT identity rendering the decoded bulk seam as
   `(B_stage − expFactor·Φ_free) − 2·BcorrWin + 2·defect` — the D.BFF.1
   skeleton at the decoded stage, with the compensator in banked profile
   form. Pure algebra over the banked route lock + P2-1 factorization.
2. Every non-B_stage constituent is controlled: `adaptiveBcorrWin` bounded
   (banked), `defect → 0` (banked eps0 gate), `expFactor` growth ≤
   `exp(admR/2)` (P2-2b), `Φ_free` compact-bounded (P2-2a).
3. Raw B on Ω? NO. B_stage − M targeted as a Prop? NO — this is an exact
   identity, not a bound.
4. Consumer: P2-4 (ε control) and P2-5 (D.BFF.4 assembly).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **P2-3a: the profile-form identity for the decoded bulk seam** (exact,
every stage, every `s`). -/
theorem decodedBulkSeam_eq_profile_form (c : ℝ) (n : ℕ) (s : ℂ) :
    decodedBulkSeam c n s
      = (galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
          - bulkProfileExpFactor n s * bulkProfileFreeM s)
        - 2 * adaptiveBcorrWin c n s
        + 2 * adaptiveGalerkinTransformDefect c n s := by
  unfold decodedBulkSeam
  rw [adaptiveFreePairedTransform_route_lock]
  rw [← compensatorM_eq_expFactor_mul_profile]
  ring

#print axioms decodedBulkSeam_eq_profile_form

end

end RHFormalization
