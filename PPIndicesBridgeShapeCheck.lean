import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge
import RHFormalization.AppendixDFiniteSpikeExtractionWitnessInstance
import RHFormalization.SelectedFiniteOperatorLayer

namespace RHFormalization

noncomputable section

#check DFiniteStageSpikeSumData
#print DFiniteStageSpikeSumData
#check DFiniteStageSpikeSumData.ppIndices

#check SelectedFiniteTraceSpikePayload
#print SelectedFiniteTraceSpikePayload
#check SelectedFiniteTraceSpikePayload.toSpikeSumData
#print SelectedFiniteTraceSpikePayload.toSpikeSumData

#check buildSelectedFiniteTraceSpikePayloadFromImageBridge
#print buildSelectedFiniteTraceSpikePayloadFromImageBridge

#check selectedAppendixDFiniteSpikeExtractionWitness.toSelectedFiniteTraceSpikePayload
#check selectedAppendixDFiniteSpikeExtractionWitness.toSelectedFiniteTraceSpikePayload.toSpikeSumData
#check selectedAppendixDFiniteSpikeExtractionWitness.toSelectedFiniteTraceSpikePayload.toSpikeSumData.ppIndices

#check buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums
#print buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums

/--
Probe 1: is `ppIndices` definitionally the image of active indices under `toPP`?
If this fails, the log tells us the exact bridge theorem needed.
-/
example (α : DFiniteStage) :
    selectedAppendixDFiniteSpikeExtractionWitness.toSelectedFiniteTraceSpikePayload.toSpikeSumData.ppIndices α =
      (selectedAppendixDFiniteSpikeExtractionWitness.activeIndices α).image
        (selectedAppendixDFiniteSpikeExtractionWitness.toPP α) := by
  rfl

/--
Probe 2: is membership in `ppIndices` equivalent to the finite image existential?
-/
example (α : DFiniteStage) (q : PrimePowerPair) :
    q ∈ selectedAppendixDFiniteSpikeExtractionWitness.toSelectedFiniteTraceSpikePayload.toSpikeSumData.ppIndices α ↔
      ∃ n ∈ selectedAppendixDFiniteSpikeExtractionWitness.activeIndices α,
        selectedAppendixDFiniteSpikeExtractionWitness.toPP α n = q := by
  constructor
  · intro hq
    simpa [Finset.mem_image] using hq
  · intro hq
    simpa [Finset.mem_image] using hq

end

end RHFormalization
