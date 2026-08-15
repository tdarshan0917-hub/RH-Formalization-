/-
DENSE SCHEDULE — Brick D6: THE DENSE ENDPOINT (Stage A finish line).
RH_from_pairedTransform_only_dense : hP_dense → RH.
Lock: densePaired = ½·B(dense) − BcorrWinDense + denseDefect (exact, ring).
B(dense) = B(admissible) (rfl, D2). Window: BcorrWinDense_uniform_bound (D5).
Defect: denseGalerkinTransformDefect_loc_bdd (D4b). Terminates in the SAME
RH_from_compensatedB_locbdd as the certified endpoint — the full
continuation/rigidity chain is inherited untouched. The certified RH
implication now lives on L = X^{3/4} = o(X), where the dilution theorem
does not apply.
-/

import RHFormalization.CompensatedBDecisiveEndpoint
import RHFormalization.DenseDefectLocBdd
import RHFormalization.DenseWindowBound
import RHFormalization.DenseGalerkinStage
import RHFormalization.GalerkinOneLetterNormalizationLock

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- **DENSE WINDOWED-CANONICAL LOCK**: the windowed package at denseL equals
½·B(admissible) − BcorrWinDense — per-spike coefficient split via the banked
`windowFactor_split`. -/
theorem dense_windowedCanonical_lock (n : ℕ) (s : ℂ) :
    windowedCanonicalPackage
        (activePrimePowerPairsCenterBelow (admR n)) (denseL n)
        shiftedLaplaceHeatKernelC s
      = (1 / 2 : ℂ) *
          galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - BcorrWinDense n s := by
  have hB : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * shiftedLaplaceHeatKernelC q.center s := rfl
  have hL0 : denseL n ≠ 0 := (denseL_pos n).ne'
  unfold windowedCanonicalPackage BcorrWinDense
  rw [hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [windowFactor_split (denseL n) q.center hL0]
  ring

/-- **DENSE ROUTE LOCK**: densePaired = ½·B(admissible) − W_dense + D_dense. -/
theorem denseFreePairedTransform_route_lock (n : ℕ) (s : ℂ) :
    denseFreePairedTransform n s
      = (1 / 2 : ℂ) *
          galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - BcorrWinDense n s
        + denseGalerkinTransformDefect n s := by
  rw [← dense_windowedCanonical_lock n s]
  unfold denseGalerkinTransformDefect
  ring

/-- **RH FROM hP ON THE DENSE SCHEDULE** — the Stage A endpoint. -/
theorem RH_from_pairedTransform_only_dense
    (hP : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
          ‖(2:ℂ) * denseFreePairedTransform n s - compensatorM n s‖ ≤ Cp) :
    RiemannHypothesis := by
  apply RH_from_compensatedB_locbdd
  intro K hK hKΩ
  obtain ⟨Cw, hWK⟩ := BcorrWinDense_uniform_bound K hK hKΩ
  obtain ⟨Cp, hPK⟩ := hP K hK hKΩ
  obtain ⟨Cd, hDK⟩ := denseGalerkinTransformDefect_loc_bdd K hKΩ hK
  refine ⟨Cp + 2 * Cw + 2 * Cd, fun n s hs => ?_⟩
  have hlock := denseFreePairedTransform_route_lock n s
  have hid : compensatedBFamily n s
      = ((2:ℂ) * denseFreePairedTransform n s - compensatorM n s)
        + (2:ℂ) * BcorrWinDense n s
        - (2:ℂ) * denseGalerkinTransformDefect n s := by
    unfold compensatedBFamily
    linear_combination (-2:ℂ) * hlock
  rw [hid]
  have key : ∀ (A W D : ℂ), ‖A + W - D‖ ≤ ‖A‖ + ‖W‖ + ‖D‖ := by
    intro A W D
    have t1 := norm_sub_le (A + W) D
    have t2 := norm_add_le A W
    linarith
  refine le_trans (key _ _ _) ?_
  have h1 := hPK n s hs
  have hw := hWK n s hs
  have hd := hDK n s hs
  have e2 : ‖(2:ℂ)‖ = 2 := by norm_num
  simp only [norm_mul, e2]
  linarith

#print axioms dense_windowedCanonical_lock
#print axioms denseFreePairedTransform_route_lock
#print axioms RH_from_pairedTransform_only_dense

end

end RHFormalization
