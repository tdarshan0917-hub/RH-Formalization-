import RHFormalization.HExplicitFormulaSplit

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

variable
  (Y : DDetailedConstructionWithOperatorLegality)
  (Zpole : ℂ → ℂ)

/--
This is the current H/E analytic frontier after `HExplicitFormulaSplit`.

Proving this turns the algebraic definition

  Harch := Y.B.Cshared.Bshared + Zpole

into a valid `HArchPackage`.
-/
example :
    HolomorphicOnC
      (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
      Ω := by
  -- This is the next real proof target.
  -- It should come from:
  --   1. meromorphicity/principal parts of `Zpole`;
  --   2. meromorphicity/principal parts of `Y.B.Cshared.Bshared`;
  --   3. cancellation of principal parts on Ω.
  sorry

end

end RHFormalization
