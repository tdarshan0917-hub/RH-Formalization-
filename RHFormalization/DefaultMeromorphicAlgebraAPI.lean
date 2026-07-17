import RHFormalization.DefaultMeromorphicAlgebra

/-!
# RHFormalization.DefaultMeromorphicAlgebraAPI

Compatibility wrapper.

The canonical implementation of `defaultMeromorphicAlgebraAPI` now lives in

  RHFormalization.DefaultMeromorphicAlgebra

This file intentionally re-exports that module without redeclaring the same
constant. It preserves older imports while avoiding duplicate declaration
collisions in `RHFormalization.lean`.
-/

namespace RHFormalization

noncomputable section

#check defaultMeromorphicAlgebraAPI
#print axioms defaultMeromorphicAlgebraAPI

end

end RHFormalization
