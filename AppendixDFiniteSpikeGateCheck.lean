import RHFormalization.AppendixDFiniteSpikeExtractionWitness

namespace RHFormalization

#print AppendixDFiniteSpikeExtractionWitness

#check DFiniteStage.diagonalSpikeActive
#check DFiniteStage.diagonalSpikeContribution
#check DFiniteStage.canonicalSpikeContribution
#check DFiniteStage.h_diagonalSpikeExtraction

-- These are expected to be unknown unless the stage already stores the needed data.
#check DFiniteStage.activeIndices
#check DFiniteStage.toPP
#check DFiniteStage.h_activeIndices_complete
#check DFiniteStage.hcoeff
#check DFiniteStage.hinj

end RHFormalization
