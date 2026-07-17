import RHFormalization.SelectedDWindowAlphaIndexData
import RHFormalization.CanonicalPrimePowerSoundCutoffCounting
import RHFormalization.SelectedFiniteOperatorLayer

namespace RHFormalization

noncomputable section

/--
If an upstream selected D-window sound-counting package exists, then it already
contains the four alpha/index fields needed for `SelectedDWindowAlphaIndexData`.
-/
def selectedDWindowAlphaIndexDataFromSoundCounting
    (S : CanonicalPrimePowerDWindowSoundCountingData selectedFiniteOperatorLayer) :
    SelectedDWindowAlphaIndexData :=
{
  alpha := S.alpha
  h_R_ge_nat := S.h_R_ge_nat
  h_indices_contains_of_center_le_R :=
    S.h_indices_contains_of_center_le_R
  h_indices_subset_center_le_R :=
    S.h_indices_subset_center_le_R
}

end

end RHFormalization
