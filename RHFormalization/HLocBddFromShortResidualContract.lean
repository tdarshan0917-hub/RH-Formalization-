import RHFormalization.AppendixDKeyFormShortContract
import RHFormalization.PrimePerturbedOperatorLayerAligned
import Mathlib

/-!
# h_loc_bdd from the short-residual contract (the chain bolt).

DUniformShortResidualBound and the Montel h_loc_bdd are the SAME proposition with
shortResidual := R_stage. This file makes that identification explicit for the
prime-perturbed aligned layer: the contract's OUTPUT (produced by
DUniformShortResidualBound_from_admissibleShortData from the three sector bounds)
becomes exactly the h_loc_bdd input that dcanrem_from_montel consumes.

This is NOT a certificate: the hypothesis is the contract OUTPUT (discharged by the
D.LOC/D.DISP/D.TAIL sector data), not the goal restated. This file only retypes the
contract conclusion to the Montel input shape.
-/

namespace RHFormalization
open Complex
open scoped BigOperators

variable {N : ℕ}

/-- **The chain bolt.** The short-residual uniform bound for `R_stage` IS the Montel
`h_loc_bdd`. Same shape, modulo the harmless `0 ≤ C` witness. -/
theorem primePerturbedAligned_h_loc_bdd_from_shortContract
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (h : DUniformShortResidualBound alpha
          (fun α s => (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage α s)) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨C, _hC0, hC⟩ := h K hK hKΩ
  exact ⟨C, hC⟩

#print axioms primePerturbedAligned_h_loc_bdd_from_shortContract

end RHFormalization
