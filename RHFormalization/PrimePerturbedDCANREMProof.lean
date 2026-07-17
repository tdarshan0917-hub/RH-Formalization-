import RHFormalization.ArithmeticShiftedLaplaceCleanDFHTarget
import RHFormalization.ArithmeticShiftedLaplaceDBcanClean
import RHFormalization.ArithmeticShiftedLaplaceIntegratedManifest

/-!
This file intentionally no longer proves `PrimePerturbedAlignedAllOmegaRStageBound`.

That target used the fixed-μ payload:

  primePerturbedOperatorLayerAligned μ

and is not the manuscript route.

The live route is the stage-coupled arithmetic route:

  arithmeticPrimeOperatorDFiniteStage n (μ n) (M n) (hnn n)

with the shifted-Laplace clean DBcan convergence already developed in the repo.
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

#check arithmeticPrimeShiftedLaplaceBStage_tendsto_Bshared_sigma1
#check arithmeticPrimeShiftedLaplaceBStage_tendsto_cleanDBcan_sigma1

#print axioms arithmeticPrimeShiftedLaplaceBStage_tendsto_Bshared_sigma1
#print axioms arithmeticPrimeShiftedLaplaceBStage_tendsto_cleanDBcan_sigma1

end
end RHFormalization
