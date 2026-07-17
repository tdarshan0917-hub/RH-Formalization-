import RHFormalization.CorrectedResolventPayload
import RHFormalization.SpectralResolventConvergence
import RHFormalization.ConcreteResolventConvergence
import RHFormalization.DirichletPWQOToOperatorEigenvalue
import RHFormalization.PrimeSideTransformKernelPrototype

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- The residual limit: RHcan = FHcan - (prime package tsum). -/
noncomputable def resolventRH : ℂ → ℂ :=
  fun s =>
    concreteDirichletPWQOData.toOperatorEigenvalueData.FHcan s
      - shiftedLaplacePrimePackage.Bshared s

#print axioms resolventRH

end
end RHFormalization
