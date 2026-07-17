import RHFormalization.CorrectedResolventPayload
import Mathlib

namespace RHFormalization
noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
This is the real D.EXPORT analytic target.

It says the spectral resolvent partial sum and the finite shifted prime package
cancel up to a compact-uniform residual on Ω.

This must eventually be proved from Appendix-D trace/Duhamel/operator estimates,
not from separate global boundedness of the prime package.
-/
def CorrectedResolventDirectCancellationBound : Prop :=
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ α : DFiniteStage,
          ∀ s : ℂ,
            s ∈ K →
              ‖spectralResolventPartial α s
                -
                finiteCanonicalPrimePowerPackage
                  (resolventIndices α)
                  shiftedLaplaceHeatKernelC
                  s‖ ≤ C

/--
If the direct cancellation estimate is supplied, then the corrected payload has
the needed R_stage compact-uniform bound.
-/
theorem correctedResolventPayload_R_stage_bound_from_direct_cancellation
    (hD : CorrectedResolventDirectCancellationBound) :
  ∀ K : Set ℂ,
    IsCompact K →
    K ⊆ Ω →
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ α : DFiniteStage,
          ∀ s : ℂ,
            s ∈ K →
              ‖correctedResolventPayload.R_stage α s‖ ≤ C := by
  intro K hK hKOmega
  obtain ⟨C, hC0, hC⟩ := hD K hK hKOmega
  refine ⟨C, hC0, ?_⟩
  intro α s hs
  simpa [correctedResolventPayload] using hC α s hs

#print axioms correctedResolventPayload_R_stage_bound_from_direct_cancellation

end
end RHFormalization
