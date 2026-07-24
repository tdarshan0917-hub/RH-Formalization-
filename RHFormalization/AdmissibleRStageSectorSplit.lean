import RHFormalization.AdmissibleHConvFromRLocBdd
import RHFormalization.AdmissibleDFHLimitData
import RHFormalization.DMRSectorTimeSplit

/-!
# AdmissibleRStageSectorSplit — BRICK A: the frontier decomposition

ROUTE CARD
1. Target: the EXACT four-sector identity with LHS literally
   `admissibleRStageFamily n s` (the h_loc_bdd object):
     R_stage = Bulk(t0) + Win + Short + Tail(t0)
   where Win = FirstOrderWindow (bound banked), Short =
   SecondResolventResidual (bound banked), Tail = −canonicalPackageTail
   (half-plane bound banked), Bulk = freeStage − canonicalPackageShort
   (THE knife-edge).
2. This theorem IS the checklist: each sector's bound status is now a
   named row. No estimate is accepted unless it closes a row.
3. Raw B on Ω? NO. hComb/CompensatedB targeted? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- Window sector (= banked FirstOrderWindow). -/
def admissibleRSectorWin (n : ℕ) (s : ℂ) : ℂ := FirstOrderWindow n s

/-- Short/residual sector (= banked SecondResolventResidual). -/
def admissibleRSectorShort (n : ℕ) (s : ℂ) : ℂ := SecondResolventResidual n s

/-- Tail sector: minus the large-time package tail at threshold t0. -/
def admissibleRSectorTail (t0 : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  - canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) t0 s

/-- **Bulk sector** (the knife-edge): free stage minus the short-time
package head at threshold t0. -/
def admissibleRSectorBulk (t0 : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  admissibleFreeStage n s
    - canonicalPackageShort (activePrimePowerPairsCenterBelow (admR n)) t0 s

/-- **BRICK A — THE EXACT SECTOR SPLIT.** -/
theorem admissibleRStageFamily_eq_sector_sum
    (t0 : ℝ) (ht0 : 0 < t0) (n : ℕ) (s : ℂ) :
    admissibleRStageFamily n s
      = admissibleRSectorBulk t0 n s
        + admissibleRSectorWin n s
        + admissibleRSectorShort n s
        + admissibleRSectorTail t0 n s := by
  have hR : admissibleRStageFamily n s
      = galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
    rfl
  have hFsplit : galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      = admissibleFreeStage n s + FirstOrderWindow n s
        + SecondResolventResidual n s := by
    first
      | exact admissible_F_stage_split n s
      | exact admissible_F_stage_eq_free_add_window_add_residual n s
      | exact F_stage_eq_free_add_first_add_second n s
      | rfl
      | (unfold FirstOrderWindow SecondResolventResidual
         ring)
  have hBid : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (admR n))
          shiftedLaplaceHeatKernelC s := by
    rfl
  have hBsplit : finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow (admR n))
        shiftedLaplaceHeatKernelC s
      = canonicalPackageShort (activePrimePowerPairsCenterBelow (admR n)) t0 s
        + canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) t0 s := by
    first
      | exact finiteCanonicalPrimePowerPackage_eq_short_add_tail
          (activePrimePowerPairsCenterBelow (admR n)) t0 ht0 s
      | exact finiteCanonicalPrimePowerPackage_eq_short_add_tail
          (activePrimePowerPairsCenterBelow (admR n)) ht0 s
      | exact finiteCanonicalPrimePowerPackage_eq_short_add_tail
          (activePrimePowerPairsCenterBelow (admR n)) t0 s
  rw [hR, hFsplit, hBid, hBsplit]
  unfold admissibleRSectorBulk admissibleRSectorWin
    admissibleRSectorShort admissibleRSectorTail
  ring

#print axioms admissibleRStageFamily_eq_sector_sum

end

end RHFormalization
