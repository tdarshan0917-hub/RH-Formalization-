import RHFormalization.SelectedDWindowAlphaIndexData
import RHFormalization.AppendixDFiniteSpikeExtractionWitnessInstance
import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration

namespace RHFormalization

noncomputable section

/--
Finite Appendix-D cutoff/exhaustion theorem for the selected stages.
This is the real missing alpha/index theorem.
-/
def appendixD_selected_alpha_index_data :
    SelectedDWindowAlphaIndexData :=
by
  refine
  {
    alpha := ?alpha
    h_R_ge_nat := ?h_R_ge_nat
    h_indices_contains_of_center_le_R := ?h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := ?h_indices_subset_center_le_R
  }

end

end RHFormalization
