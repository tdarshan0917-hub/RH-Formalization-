import RHFormalization.CorrectedResolventPayload
import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.CanonicalPrimePowerPackage

namespace RHFormalization
noncomputable section
open Complex

noncomputable def resKernel : CanonicalKernelC :=
  fun a s => (s + ((a : ℂ)))⁻¹

-- Direct equality test: does the eigenvalue range-sum equal the prime-pair package?
example (α : DFiniteStage) (s : ℂ) :
    spectralResolventPartial α s =
      finiteCanonicalPrimePowerPackage (resolventIndices α) resKernel s := by
  unfold spectralResolventPartial finiteCanonicalPrimePowerPackage resolventIndices
  sorry

end
end RHFormalization
