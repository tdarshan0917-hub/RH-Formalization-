import RHFormalization.PrimeDUSRAssembly
import RHFormalization.PrimePerturbedDMasterResidualAligned
import RHFormalization.DCanRemFromMontel
import Mathlib

/-!
# Prime D.USR to Montel target

D.USR now gives `h_loc_bdd`.
This file pins the remaining Montel input for the aligned prime layer:
the overlap convergence `h_overlap`.

Do not use the old `resolvent_h_conv_absConv` directly; it is for the free resolvent route.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/-- Exact overlap input needed for the aligned prime layer. -/
def PrimePerturbedAlignedOverlap
    (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (R_H : ℂ → ℂ) : Prop :=
  ∃ U : Set ℂ,
    IsOpen U ∧
    U.Nonempty ∧
    U ⊆ Ω ∧
      ∀ s ∈ U,
        Filter.Tendsto
          (fun n =>
            (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
              (alpha n) s)
          atTop
          (nhds (R_H s))

/-- D.USR plus overlap gives the DMasterResidualData input. -/
def primePerturbedDMasterResidual_from_DUSR_and_overlap
    (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (R_H : ℂ → ℂ)
    (hpos :
      ∀ α : DFiniteStage,
      ∀ i,
        0 ≤ perturbedEigenvalues μ
          (primePotential_isHermitian
            (primeStageWeights (primePerturbedStageIndex α))) i)
    (Qloc Qdisp Rtail : DFiniteStage → ℂ → ℂ)
    (anchor : ℕ → ℝ)
    (factor : Set ℂ → ℝ)
    (h_anchor_nonneg : ∀ n, 0 ≤ anchor n)
    (h_anchor_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ n, anchor n ≤ A)
    (h_factor_nonneg : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → 0 ≤ factor K)
    (h_decomp : ∀ n s,
        (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s
          = Qloc (alpha n) s + Qdisp (alpha n) s + Rtail (alpha n) s)
    (h_loc_le :
      ∀ K, IsCompact K → K ⊆ Ω →
        ∀ n, ∀ s ∈ K, ‖Qloc (alpha n) s‖ ≤ anchor n * factor K)
    (h_disp_le :
      ∀ K, IsCompact K → K ⊆ Ω →
        ∀ n, ∀ s ∈ K, ‖Qdisp (alpha n) s‖ ≤ anchor n * factor K)
    (h_tail_le :
      ∀ K, IsCompact K → K ⊆ Ω →
        ∀ n, ∀ s ∈ K, ‖Rtail (alpha n) s‖ ≤ anchor n * factor K)
    (h_overlap : PrimePerturbedAlignedOverlap μ alpha R_H)
    (hMontel :
      HolomorphicMontelConvergence
        (fun n s =>
          (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
            (alpha n) s)
        R_H) :
    DMasterResidualData
      (primePerturbedOperatorLayerAligned μ).toStagePackage := by
  have h_stage_holo :
      ∀ n : ℕ,
        HolomorphicOnC
          (fun s =>
            (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
              (alpha n) s) Ω :=
    fun n => primePerturbedAligned_stage_holo μ hpos (alpha n)

  have h_loc_bdd :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∃ C : ℝ,
            ∀ n : ℕ,
            ∀ s : ℂ,
              s ∈ K →
                ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage
                  (alpha n) s‖ ≤ C :=
    primePerturbedAligned_h_loc_bdd_from_three_sectors
      μ alpha Qloc Qdisp Rtail anchor factor
      h_anchor_nonneg h_anchor_bound h_factor_nonneg
      h_decomp h_loc_le h_disp_le h_tail_le

  exact dcanrem_from_montel
    (primePerturbedOperatorLayerAligned μ).toStagePackage
    alpha
    R_H
    h_stage_holo
    h_loc_bdd
    h_overlap
    hMontel

#print axioms PrimePerturbedAlignedOverlap
#print axioms primePerturbedDMasterResidual_from_DUSR_and_overlap

end
end RHFormalization
