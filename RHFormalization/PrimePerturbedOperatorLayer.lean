import RHFormalization.PrimePerturbedPayload
import RHFormalization.SelectedFiniteCanonicalPayload
import RHFormalization.ResolventOperatorLayer
import Mathlib

/-!
# Prime-perturbed operator layer (the RIGHT operator the spine consumes)

Wraps `primePerturbedPayload` (F = genuine prime-perturbed operator) into the
operator layer, exactly as `resolventOperatorLayer` wrapped the free payload.
This is the missing layer object: the spine chain (R → O → bridge → H-side)
now consumes the CORRECT operator.
-/

namespace RHFormalization
open Complex

/-- **Prime-perturbed operator layer.** Right-operator analog of `resolventOperatorLayer`. -/
noncomputable def primePerturbedOperatorLayer (μ : Fin N → ℝ) :
    DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromCanonicalPayload (primePerturbedPayload μ)

#print axioms primePerturbedOperatorLayer

end RHFormalization
