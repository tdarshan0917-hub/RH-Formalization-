import RHFormalization.FinalConditionalSpine

set_option pp.all true
set_option pp.universes true

namespace RHFormalization

-- A. Print the exact top-level RH spine signature.
#check @finalConditionalRHSpine

-- B. Print axiom dependencies of the final conditional spine.
#print axioms finalConditionalRHSpine

-- C. Intentionally ask Lean: what is still missing if we try to prove RH now?
-- The unsolved goals here are the top-level remaining inputs.
example : RiemannHypothesis :=
  finalConditionalRHSpine ?ZF ?Y ?X ?E ?ONFP

end RHFormalization
