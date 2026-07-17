import RHFormalization.AppendixDFiniteSpikeExtractionWitnessInstance

/-!
# Selected finite operator layer

The selected finite operator layer is built from the selected Appendix-D finite
spike extraction witness.
-/

namespace RHFormalization

noncomputable section

def selectedFiniteOperatorLayer :
    DFiniteStagePackageFromOperatorLayer :=
  selectedAppendixDFiniteSpikeExtractionWitness.toSelectedFiniteOperatorLayer

end

end RHFormalization
