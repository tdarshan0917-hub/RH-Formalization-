import RHFormalization.DOperatorExport

/-!
# Appendix D: KEY-FORM-SHORT contract (reduction only)

Records the clean reduction:
  admissible density-normalized anchor bound  ⇒  uniform short-residual bound on Ω-compacts.
This does NOT prove the hard anchor estimate; that is
`buildDAdmissibleShortResidualData_from_AppendixD_estimates`, deferred.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter
open scoped BigOperators

/-- Uniform compact bound for a short-time residual family along an ordered stage net. -/
def DUniformShortResidualBound
    (alpha : ℕ → DFiniteStage) (shortResidual : DFiniteStage → ℂ → ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K → ‖shortResidual (alpha n) s‖ ≤ C

/-- Admissible short-residual data (formal D.ADM / D.KEY-FORM-SHORT contract). -/
structure DAdmissibleShortResidualData where
  alpha : ℕ → DFiniteStage
  shortResidual : DFiniteStage → ℂ → ℂ
  densityAnchor : ℕ → ℝ
  compactFactor : Set ℂ → ℝ
  h_densityAnchor_nonneg : ∀ n : ℕ, 0 ≤ densityAnchor n
  h_densityAnchor_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, densityAnchor n ≤ A
  h_compactFactor_nonneg : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → 0 ≤ compactFactor K
  h_shortResidual_le :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
      ‖shortResidual (alpha n) s‖ ≤ densityAnchor n * compactFactor K

/-- D.KEY-FORM-SHORT reduction: uniform anchor ⇒ uniform short-residual bound. -/
theorem DUniformShortResidualBound_from_admissibleShortData
    (D : DAdmissibleShortResidualData) :
    DUniformShortResidualBound D.alpha D.shortResidual := by
  intro K hK hKOmega
  rcases D.h_densityAnchor_bound with ⟨A, hA_nonneg, hA_bound⟩
  refine ⟨A * D.compactFactor K, mul_nonneg hA_nonneg (D.h_compactFactor_nonneg K hK hKOmega), ?_⟩
  intro n s hs
  exact le_trans (D.h_shortResidual_le K hK hKOmega n s hs)
    (mul_le_mul_of_nonneg_right (hA_bound n) (D.h_compactFactor_nonneg K hK hKOmega))

#print axioms DUniformShortResidualBound_from_admissibleShortData
end
end RHFormalization
