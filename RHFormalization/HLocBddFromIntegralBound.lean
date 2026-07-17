import RHFormalization.AlongNetBoundFromQRes
import RHFormalization.ResidualLaplaceRep
import Mathlib

/-!
# hQ from the Stieltjes identity + a cutoff-independent ∫|Q_res| bound (D.USR final assembly).

‖R_stage‖ = ‖∫ e^{-st} Q_res‖ ≤ ∫|Q_res| ≤ C (cutoff-independent).
The first step is the Stieltjes identity (green mod connector); the second is the
triangle inequality; the third is the banked Galerkin/Duhamel uniform bound.

Packaged so hQ reduces to ONE cutoff-independent integral bound hQint, which the
banked Galerkin uniform bound supplies. This closes h_loc_bdd modulo:
  - the named Gaussian connector (inside the Stieltjes rep)
  - hQint (the cutoff-independent ∫|Q_res| ≤ C, = banked Galerkin bound)
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- **hQ assembly.** Given (a) the Stieltjes representation of R_stage as the Laplace
transform of Q_res on K, and (b) a cutoff-independent bound on ∫|Q_res|, the uniform
R_stage bound hQ follows by the triangle inequality. -/
theorem primePerturbedAligned_qRes_bound_from_integral_bound
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (hRep : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
      (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s
        = ∫ t in Set.Ioi (0:ℝ), qResIntegrand (primePerturbedStageIndex (alpha n)) μ (alpha n) s t)
    (hQint : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        (∫ t in Set.Ioi (0:ℝ),
          ‖qResIntegrand (primePerturbedStageIndex (alpha n)) μ (alpha n) s t‖) ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨C, hC0, hC⟩ := hQint K hK hKΩ
  refine ⟨C, hC0, ?_⟩
  intro n s hs
  rw [hRep K hK hKΩ n s hs]
  calc ‖∫ t in Set.Ioi (0:ℝ), qResIntegrand (primePerturbedStageIndex (alpha n)) μ (alpha n) s t‖
      ≤ ∫ t in Set.Ioi (0:ℝ),
          ‖qResIntegrand (primePerturbedStageIndex (alpha n)) μ (alpha n) s t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ C := hC n s hs

/-- **h_loc_bdd from the Stieltjes rep + cutoff-independent integral bound.** -/
theorem primePerturbedAligned_h_loc_bdd_from_integral_bound
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (hRep : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
      (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s
        = ∫ t in Set.Ioi (0:ℝ), qResIntegrand (primePerturbedStageIndex (alpha n)) μ (alpha n) s t)
    (hQint : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        (∫ t in Set.Ioi (0:ℝ),
          ‖qResIntegrand (primePerturbedStageIndex (alpha n)) μ (alpha n) s t‖) ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C :=
  primePerturbedAligned_h_loc_bdd_from_qRes_bound μ alpha
    (primePerturbedAligned_qRes_bound_from_integral_bound μ alpha hRep hQint)

#print axioms primePerturbedAligned_h_loc_bdd_from_integral_bound

end RHFormalization
