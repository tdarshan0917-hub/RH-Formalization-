import RHFormalization.CorrectedResolventPayload
import RHFormalization.SelectedFiniteCanonicalPayload

namespace RHFormalization
noncomputable section

/-- The resolvent finite-operator layer, built from the corrected payload. -/
noncomputable def resolventOperatorLayer : DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromCanonicalPayload correctedResolventPayload

#print axioms resolventOperatorLayer

end
end RHFormalization
