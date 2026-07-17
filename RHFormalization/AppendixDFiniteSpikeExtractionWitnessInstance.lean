import RHFormalization.AppendixDFiniteSpikeExtractionWitness

/-!
# Selected Appendix-D finite spike extraction witness instance

This builds the selected finite Appendix-D witness by projecting the finite
spike certificate stored in each `DFiniteStage`.
-/

namespace RHFormalization

noncomputable section

def selectedAppendixDFiniteSpikeExtractionWitness :
    AppendixDFiniteSpikeExtractionWitness :=
{
  F_stage := fun α => α.appendixDFiniteFStage

  activeIndices := fun α => α.diagonalSpikeActiveIndices

  h_activeIndices_active := by
    intro α q hq
    exact α.h_diagonalSpikeActiveIndices_active q hq

  h_activeIndices_complete := by
    intro α q hq
    exact α.h_diagonalSpikeActiveIndices_complete q hq

  toPP := fun α => α.diagonalSpikeToPP

  hinj := by
    intro α m hm n hn hmn
    exact α.h_diagonalSpikeToPP_inj m hm n hn hmn

  hcoeff := by
    intro α n hn
    exact α.h_canonicalSpikeContribution_eq_weightC n hn
}

end

end RHFormalization
