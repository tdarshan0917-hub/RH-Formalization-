import RHFormalization.CorrectedResidualBoundReduction
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- F-side target: spectral resolvent partial sums are compact-uniformly bounded. -/
theorem correctedResolvent_F_bound_target :
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ CF : ℝ,
        0 ≤ CF ∧
          ∀ α : DFiniteStage,
          ∀ s : ℂ,
            s ∈ K →
              ‖spectralResolventPartial α s‖ ≤ CF := by
  intro K hK hKOmega
  unfold spectralResolventPartial
  trace_state
  fail

/-- B-side target: finite shifted prime package is compact-uniformly bounded. -/
theorem correctedResolvent_B_bound_target :
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ CB : ℝ,
        0 ≤ CB ∧
          ∀ α : DFiniteStage,
          ∀ s : ℂ,
            s ∈ K →
              ‖finiteCanonicalPrimePowerPackage
                  (resolventIndices α)
                  shiftedLaplaceHeatKernelC
                  s‖ ≤ CB := by
  intro K hK hKOmega
  unfold resolventIndices
  trace_state
  fail

end
end RHFormalization
