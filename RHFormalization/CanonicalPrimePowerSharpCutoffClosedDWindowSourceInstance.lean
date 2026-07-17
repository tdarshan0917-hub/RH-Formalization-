import RHFormalization.CanonicalPrimePowerSharpCutoffClosedDWindowSource

/-!
# Selected sharp-cutoff closed D-window source instance

This is the current real Appendix-D source target.

Do not go through the R-cutoff detailed-construction bypass here.
That route asks for the whole detailed construction at once.

The intended source object is the closed D-window source feeding the
heat-kernel weighted / chosen-length D-side construction.
-/

namespace RHFormalization

noncomputable section

def selectedSharpCutoffClosedDWindowSource :
    SelectedSharpCutoffClosedDWindowSource :=
by
  refine
  {
    S := ?S
    hW := ?hW
    hKshared := ?hKshared
    sharpSpeed := ?sharpSpeed
    hL_chosen := ?hL_chosen
  }

end

end RHFormalization
