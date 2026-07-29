import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.ConcreteThreeSectorProviderTarget
import Mathlib

/-!
# BRICK 1: exact three-sector decomposition of the aligned R_stage

CONSUMER (named per Section 0 rule): the `h_decomp` conjunct of
`ConcreteThreeSectorProviderTarget` and the `h_decomp` hypothesis of
`primePerturbedDMasterResidual_from_DUSR_and_overlap`.

Sectors (frozen to the measured numerics of 2026-07):
  Rtail  := free resolvent trace  FstageFinite μ            (stage-independent)
  Qdisp  := F_pert − F_free − firstOrder                    (k ≥ 2 Duhamel words)
  Qloc   := firstOrder − arithmeticShiftedLaplaceBStage     (one-letter vs spike seam)

The identity Qloc + Qdisp + Rtail = F_pert − B = R_stage is exact algebra:
firstOrder and FstageFinite each occur once with each sign.
-/

namespace RHFormalization
noncomputable section
open Complex
open scoped BigOperators

variable {N : ℕ}

/-- Tail sector: the free (unperturbed) resolvent trace. Stage-independent. -/
noncomputable def alignedRtail (μ : Fin N → ℝ) (_α : DFiniteStage) (s : ℂ) : ℂ :=
  FstageFinite μ s

/-- Exact diagonal one-letter (first Duhamel word) term:
`−Σ_i w_i / (s + μ_i)^2` with the stage weights. -/
noncomputable def alignedFirstOrder (μ : Fin N → ℝ) (α : DFiniteStage) (s : ℂ) : ℂ :=
  -∑ i, ((primeStageWeights (primePerturbedStageIndex α) i : ℂ) /
      ((s + (μ i : ℂ)) ^ 2))

/-- Displacement sector: perturbed minus free minus first-order (the k ≥ 2 word remainder). -/
noncomputable def alignedQdisp (μ : Fin N → ℝ) (α : DFiniteStage) (s : ℂ) : ℂ :=
  primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s
    - FstageFinite μ s
    - alignedFirstOrder μ α s

/-- Local sector: first-order word minus the arithmetic spike sum (the seam). -/
noncomputable def alignedQloc (μ : Fin N → ℝ) (α : DFiniteStage) (s : ℂ) : ℂ :=
  alignedFirstOrder μ α s - arithmeticShiftedLaplaceBStage α s

/-- Definitional unfolding of the aligned `R_stage`: the builder passes the payload's
`R_stage` field through unchanged, so this is `rfl`. -/
theorem primePerturbedAligned_R_stage_unfold
    (μ : Fin N → ℝ) (α : DFiniteStage) (s : ℂ) :
    (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s =
      primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s -
        arithmeticShiftedLaplaceBStage α s :=
  rfl

/-- **BRICK 1 (h_decomp).** Exact three-sector decomposition of the aligned residual,
in the exact shape consumed by `ConcreteThreeSectorProviderTarget`. -/
theorem primePerturbedAligned_three_sector_decomp
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage) :
    ∀ (n : ℕ) (s : ℂ),
      (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s =
        alignedQloc μ (alpha n) s + alignedQdisp μ (alpha n) s
          + alignedRtail μ (alpha n) s := by
  intro n s
  rw [primePerturbedAligned_R_stage_unfold]
  unfold alignedQloc alignedQdisp alignedRtail
  ring

#print axioms primePerturbedAligned_R_stage_unfold
#print axioms primePerturbedAligned_three_sector_decomp

-- SENTINEL: BRICK1-DECOMP-v2
end
end RHFormalization
