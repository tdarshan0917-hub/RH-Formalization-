import RHFormalization.OmegaConnected

/-!
# RHFormalization.DefaultConnectedOmegaAPI

Compatibility wrapper.

The canonical implementation of `defaultConnectedOmegaAPI` now lives in

  RHFormalization.OmegaConnected

This file intentionally re-exports that module without redeclaring the same
constant. It preserves older imports while avoiding duplicate declaration
collisions in `RHFormalization.lean`.
-/

namespace RHFormalization

noncomputable section

#check defaultConnectedOmegaAPI
#print axioms defaultConnectedOmegaAPI

end

end RHFormalization
