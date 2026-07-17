import RHFormalization.BuildAdmissibleShortFromEstimates
import RHFormalization.HLocBddFromShortResidualContract
import RHFormalization.AppendixDKeyFormShortContract
import RHFormalization.PrimePerturbedOperatorLayerAligned
import Mathlib

/-!
# Prime-layer D.USR assembly: three sector bounds -> h_loc_bdd.

Chains the three proven theorem-links:
  three sector bounds (D.LOC/D.DISP/D.TAIL, shared anchor*factor form) + decomposition
    -> buildDAdmissibleShortResidualData_from_AppendixD_estimates  (BUILDER)
    -> DUniformShortResidualBound_from_admissibleShortData          (CONSUMER)
    -> primePerturbedAligned_h_loc_bdd_from_shortContract           (BOLT)
    -> h_loc_bdd  (the Montel input, last open arg of the RH chain).

The three sector bounds and the decomposition are the manuscript's Appendix-D D.USR
estimates (named premises). h_loc_bdd is DERIVED through proven links, not assumed.
-/

namespace RHFormalization
open Complex
open scoped BigOperators

variable {N : ℕ}

/-- **Prime D.USR assembly.** The three uniform sector bounds + decomposition give h_loc_bdd. -/
theorem primePerturbedAligned_h_loc_bdd_from_three_sectors
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (Qloc Qdisp Rtail : DFiniteStage → ℂ → ℂ)
    (anchor : ℕ → ℝ) (factor : Set ℂ → ℝ)
    (h_anchor_nonneg : ∀ n, 0 ≤ anchor n)
    (h_anchor_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ n, anchor n ≤ A)
    (h_factor_nonneg : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → 0 ≤ factor K)
    (h_decomp : ∀ n s,
        (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s
          = Qloc (alpha n) s + Qdisp (alpha n) s + Rtail (alpha n) s)
    (h_loc_le : ∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K, ‖Qloc (alpha n) s‖ ≤ anchor n * factor K)
    (h_disp_le : ∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K, ‖Qdisp (alpha n) s‖ ≤ anchor n * factor K)
    (h_tail_le : ∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K, ‖Rtail (alpha n) s‖ ≤ anchor n * factor K) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C := by
  -- BUILDER: three sectors -> contract
  let D := buildDAdmissibleShortResidualData_from_AppendixD_estimates
    alpha
    (fun α s => (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s)
    Qloc Qdisp Rtail anchor factor
    h_anchor_nonneg h_anchor_bound h_factor_nonneg
    h_decomp h_loc_le h_disp_le h_tail_le
  -- CONSUMER: contract -> uniform short-residual bound
  have huniform := DUniformShortResidualBound_from_admissibleShortData D
  -- BOLT: uniform short-residual bound -> h_loc_bdd
  exact primePerturbedAligned_h_loc_bdd_from_shortContract μ alpha huniform

#print axioms primePerturbedAligned_h_loc_bdd_from_three_sectors

end RHFormalization
