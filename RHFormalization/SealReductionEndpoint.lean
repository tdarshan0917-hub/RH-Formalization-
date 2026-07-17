-- SENTINEL: seal-reduction-v1
import RHFormalization.CompensatedBDecisiveEndpoint
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.AdaptiveDefectLocBdd
import Mathlib

/-!
# SEAL REDUCTION — RH from the free paired transform vs compensator
Lock (banked): paired = ½·B_adaptive − W + D  ⟹  B = 2·paired + 2W − 2D.
B(adaptive) = B(admissible) (rfl). Defect D loc-bdd: BANKED.
⟹ ‖B − M‖ ≤ ‖2·paired − M‖ + 2‖W‖ + 2‖D‖.
Inputs: hP (2·paired − M bound — THE FRONTIER, free-spectrum calculus) and
hW (adaptive window bound — mechanical; admissible version banked, transfer
pending). Arithmetic starObject leaves the frontier entirely.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- **RH from the paired-transform/compensator bound (+ window transfer).** -/
theorem RH_from_pairedTransform_locbdd (c : ℝ)
    (hW : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cw : ℝ, ∀ n, ∀ s ∈ K, ‖adaptiveBcorrWin c n s‖ ≤ Cw)
    (hP : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
          ‖(2:ℂ) * adaptiveFreePairedTransform c n s - compensatorM n s‖ ≤ Cp) :
    RiemannHypothesis := by
  apply RH_from_compensatedB_locbdd
  intro K hK hKΩ
  obtain ⟨Cw, hWK⟩ := hW K hK hKΩ
  obtain ⟨Cp, hPK⟩ := hP K hK hKΩ
  obtain ⟨Cd, hDK⟩ := adaptiveGalerkinTransformDefect_loc_bdd c K hKΩ hK
  refine ⟨Cp + 2 * Cw + 2 * Cd, fun n s hs => ?_⟩
  have hlock := adaptiveFreePairedTransform_route_lock c n s
  have hBB : galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
      = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
    first
      | rfl
      | (show finiteCanonicalPrimePowerPackage
            (activePrimePowerPairsCenterBelow (adaptiveGalerkinStageSeq c n).R)
            shiftedLaplaceHeatKernelC s = _
         rfl)
  have hid : compensatedBFamily n s
      = ((2:ℂ) * adaptiveFreePairedTransform c n s - compensatorM n s)
        + (2:ℂ) * adaptiveBcorrWin c n s
        - (2:ℂ) * adaptiveGalerkinTransformDefect c n s := by
    unfold compensatedBFamily
    rw [← hBB]
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

#print axioms RH_from_pairedTransform_locbdd

end

end RHFormalization
