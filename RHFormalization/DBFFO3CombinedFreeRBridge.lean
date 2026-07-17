import RHFormalization.DBFFO3AssemblyInputs

/-!
# DBFFO3CombinedFreeRBridge

ROUTE CARD
1. Target: correct the final O3 assembly split.
2. Object: the combined cancellation term
      (admissibleFreeStage − compensatorM) − R_stage.
3. Raw B on Ω? NO.
4. R = F − raw B forced globally? NO.
5. True outright: algebraic consequence of the banked F-M-R bridge and O2
   short-residual boundedness.
6. Manuscript: D.OP-BOUND / D.TAIL-DENSITY / D.UNIFORM-CAN.
7. Consumer: parabola-depth O3 / hstar.

Why this file exists:
`DBFFO3AssemblyInputs` gave a sufficient split into separate `Hfree` and `HR`.
That split is likely too strong. The actual cancellation needed by the manuscript
is the combined object

  (admissibleFreeStage n s − compensatorM n s) − R_stage n s.

This file reduces hstar to that combined bound plus the already-banked O2 short
residual bound.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- The final combined free/R-stage cancellation bound needed for O3. -/
def DBFFO3CombinedFreeRBound : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ Cfr : ℝ,
      ∀ n : ℕ, ∀ s ∈ K,
        ‖(admissibleFreeStage n s - compensatorM n s)
            - galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖
          ≤ Cfr

/--
Combined free/R bound plus the banked O2 short-residual bound gives compensated-B
boundedness.
-/
theorem DBFFO3_compensatedB_bound_from_combined_free_R
    (HFR : DBFFO3CombinedFreeRBound) :
    DBFFO3CompensatedBBound := by
  intro K hK hKO
  obtain ⟨Cfr, hfr⟩ := HFR K hK hKO
  obtain ⟨Cshort, hshort⟩ := DBFFO3_shortResidual_bounded K hK hKO
  refine ⟨Cfr + Cshort, ?_⟩
  intro n s hs

  let A : ℂ :=
    (admissibleFreeStage n s - compensatorM n s)
      - galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
  let B : ℂ := DBFFO2ShortResidual n s

  have hEq : DBFFO3CompensatedB n s = A + B := by
    rw [DBFFO3_compensatedB_eq_FMR n (s := s) (hKO hs)]
    simp [A, B]
    ring

  have hA : ‖A‖ ≤ Cfr := by
    simpa [A] using hfr n s hs
  have hB : ‖B‖ ≤ Cshort := by
    simpa [B] using hshort n s hs

  calc
    ‖DBFFO3CompensatedB n s‖
        = ‖A + B‖ := by rw [hEq]
    _ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    _ ≤ Cfr + Cshort := add_le_add hA hB

/-- Global O3/hstar from the combined free/R cancellation bound. -/
theorem DBFFO3Hstar_from_combined_free_R
    (HFR : DBFFO3CombinedFreeRBound) :
    DBFFO3Hstar :=
  DBFFO3Hstar_from_compensatedB_bound
    DBFFO3_sqrtFactorBound
    (DBFFO3_compensatedB_bound_from_combined_free_R HFR)

/-- Parabola-depth O3/hstar from the combined free/R cancellation bound. -/
theorem DBFFO3ParabolaDepthHstar_from_combined_free_R
    (HFR : DBFFO3CombinedFreeRBound) :
    DBFFO3ParabolaDepthHstar := by
  intro K hK hKO hdepth
  exact (DBFFO3Hstar_from_combined_free_R HFR) K hK hKO

#print axioms DBFFO3CombinedFreeRBound
#print axioms DBFFO3_compensatedB_bound_from_combined_free_R
#print axioms DBFFO3Hstar_from_combined_free_R
#print axioms DBFFO3ParabolaDepthHstar_from_combined_free_R

end

end RHFormalization
