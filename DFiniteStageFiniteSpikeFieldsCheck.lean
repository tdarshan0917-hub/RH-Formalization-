import RHFormalization.DFiniteStageOperator
import RHFormalization.AppendixDSpikeSumExtraction

namespace RHFormalization

#print DFiniteStage

#check DFiniteStage.diagonalSpikeActive
#check DFiniteStage.diagonalSpikeContribution
#check DFiniteStage.canonicalSpikeContribution
#check DFiniteStage.h_diagonalSpikeExtraction

-- These are expected to be unknown unless the actual finite extraction payload exists somewhere.
#check DFiniteStage.activeIndices
#check DFiniteStage.spikeKernel
#check DFiniteStage.ppIndices
#check DFiniteStage.ppKernel

end RHFormalization
