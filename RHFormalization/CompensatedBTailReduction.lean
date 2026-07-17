-- SENTINEL: tail-reduction-v1
import RHFormalization.CompensatedBDecisiveEndpoint
import RHFormalization.GalerkinCanonicalResidualBound
import RHFormalization.GalerkinTailSplit
import Mathlib

/-!
# TAIL REDUCTION — RH from the tail sector alone
Chain (all identities exact, all bounds banked):
  B − M = (F + BcorrWin) − (R + BcorrWin + M)          [C3 identity, rearranged]
  R + BcorrWin + M = galHead + (R − galHead + BcorrWin + M)   [definitional]
Banked: F bound, BcorrWin bound, HEAD bound (any parabola depth).
⟹ loc-bdd(compensatedB) ⇐ loc-bdd(tailSector), tailSector := R − head + BcorrWin + M.
⟹ RiemannHypothesis ⇐ ONE bound on the tail sector — the open analytic brick
   (closed-form tail vs compensator asymptotics; numerically flat, 5 decades).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- The tail sector: everything in the corrected residual beyond the banked head. -/
def tailSectorFamily (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
    - galHead n s + BcorrWin n s + compensatorM n s

/-- Corrected residual = head + tailSector (definitional algebra). -/
theorem correctedResidual_eq_head_add_tailSector (n : ℕ) (s : ℂ) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      + BcorrWin n s + compensatorM n s
    = galHead n s + tailSectorFamily n s := by
  unfold tailSectorFamily
  ring

/-- **Corrected residual loc-bdd from tail sector loc-bdd** — head is banked. -/
theorem correctedResidual_locbdd_of_tailSector
    (hT : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖tailSectorFamily n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ s ∈ K,
        ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
          + BcorrWin n s + compensatorM n s‖ ≤ C := by
  intro K hK hKΩ
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, by simp [hE]⟩
  obtain ⟨Ch, _hCh0, hHead⟩ := galQRes_head_integral_bound K hK hne
  obtain ⟨Ct, hTail⟩ := hT K hK hKΩ
  refine ⟨Ch + Ct, fun n s hs => ?_⟩
  rw [correctedResidual_eq_head_add_tailSector]
  calc ‖galHead n s + tailSectorFamily n s‖
      ≤ ‖galHead n s‖ + ‖tailSectorFamily n s‖ := norm_add_le _ _
    _ ≤ Ch + Ct := add_le_add (hHead n s hs) (hTail n s hs)

/-- **Compensated-B loc-bdd from corrected residual loc-bdd** — F and BcorrWin banked. -/
theorem compensatedB_locbdd_of_correctedResidual
    (hR : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K,
          ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
            + BcorrWin n s + compensatorM n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖compensatedBFamily n s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨CF, _hCF0, hF⟩ := F_stage_uniform_bound_on_compacts K hK hKΩ
  obtain ⟨Cw, _hCw0, hw⟩ := BcorrWin_uniform_bound K hK hKΩ
  obtain ⟨CR, hRK⟩ := hR K hK hKΩ
  refine ⟨CF + Cw + CR, fun n s hs => ?_⟩
  have hmem : s ∈ Ω := hKΩ hs
  have hid : compensatedBFamily n s
      = (galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          + BcorrWin n s)
        - (galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
            + BcorrWin n s + compensatorM n s) := by
    have h := canonicalResidual_eq_F_sub_star n s hmem
    unfold compensatedBFamily
    first
      | linarith [h]
      | (rw [h]; ring)
      | (have := h; ring_nf; ring_nf at this; linarith [this])
      | (unfold compensatedBFamily at *; linear_combination h)
  rw [hid]
  calc ‖(galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          + BcorrWin n s)
        - (galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
            + BcorrWin n s + compensatorM n s)‖
      ≤ ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          + BcorrWin n s‖
        + ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
            + BcorrWin n s + compensatorM n s‖ := norm_sub_le _ _
    _ ≤ (‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s‖
          + ‖BcorrWin n s‖) + CR :=
          add_le_add (norm_add_le _ _) (hRK n s hs)
    _ ≤ (CF + Cw) + CR := add_le_add (add_le_add (hF n s hs) (hw n s hs)) le_rfl
    _ = CF + Cw + CR := by ring

/-- **THE REDUCED DECISIVE ENDPOINT: RH from the tail sector alone.** -/
theorem RH_from_tailSector_locbdd
    (hT : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖tailSectorFamily n s‖ ≤ C) :
    RiemannHypothesis :=
  RH_from_compensatedB_locbdd
    (compensatedB_locbdd_of_correctedResidual
      (correctedResidual_locbdd_of_tailSector hT))

#print axioms tailSectorFamily
#print axioms correctedResidual_eq_head_add_tailSector
#print axioms correctedResidual_locbdd_of_tailSector
#print axioms compensatedB_locbdd_of_correctedResidual
#print axioms RH_from_tailSector_locbdd

end

end RHFormalization
