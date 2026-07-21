import RHFormalization.HtailFrontier
import RHFormalization.DBFFBcorr
import RHFormalization.DBFFAdmissibleRStageOverlap
import RHFormalization.AdmissibleRStageHolo
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter Topology

/--
The finite canonical corrected remainder in the live admissible coordinates.

This is the only finite-stage family considered from this point:
`R_stage + Bcorr`.
-/
noncomputable def canonicalRcanStage (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.R_stage
      (admissibleGalerkinStageSeq n) s
    + Bcorr n s

/--
Exact canonical algebra:
Rcan = F_stage - (B_stage - Bcorr).
-/
theorem canonicalRcanStage_eq_F_sub_correctedB
    (n : ℕ) (s : ℂ) :
    canonicalRcanStage n s
      =
    galerkinStagePackage.F_stage
        (admissibleGalerkinStageSeq n) s
      -
    (galerkinStagePackage.B_stage
        (admissibleGalerkinStageSeq n) s
      - Bcorr n s) := by
  unfold canonicalRcanStage
  change
    (galerkinStagePackage.F_stage
        (admissibleGalerkinStageSeq n) s
      -
     galerkinStagePackage.B_stage
        (admissibleGalerkinStageSeq n) s)
      + Bcorr n s
      =
    galerkinStagePackage.F_stage
        (admissibleGalerkinStageSeq n) s
      -
    (galerkinStagePackage.B_stage
        (admissibleGalerkinStageSeq n) s
      - Bcorr n s)
  ring

/-- Every finite canonical remainder stage is Ω-holomorphic. -/
theorem canonicalRcanStage_holo (n : ℕ) :
    HolomorphicOnC (canonicalRcanStage n) Ω := by
  intro z hz
  exact
    (admissible_R_stage_holo n z hz).add
      (Bcorr_holo n z hz)

/--
The finite canonical remainder stages already have the exact live overlap
limit required for R_H^can.
-/
theorem canonicalRcanStage_overlap_tendsto
    (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ => canonicalRcanStage n s)
      atTop
      (𝓝
        (FHadmFree s
          - galerkinBcanLimitData.Bcan s)) := by
  have hR := admissible_R_stage_to_DBFF_overlap s hs
  have hB := Bcorr_overlap0 hs
  simpa [canonicalRcanStage] using hR.add hB

#print axioms canonicalRcanStage_eq_F_sub_correctedB
#print axioms canonicalRcanStage_holo
#print axioms canonicalRcanStage_overlap_tendsto

end

end RHFormalization
