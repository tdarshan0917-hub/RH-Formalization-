import RHFormalization.HExplicitFormulaSplit
import RHFormalization.PrincipalPartMeromorphic
import RHFormalization.PrincipalPartCoboundedModel
import RHFormalization.HSideResidueArithmetic
import RHFormalization.HSidePoleWitness

/-!
# RHFormalization.HExplicitFormulaHolomorphy

Current H/E analytic frontier.

After `HExplicitFormulaSplit`, the H-side split is algebraic.
The remaining theorem is the cancellation/holomorphy statement:

  HolomorphicOnC (fun s => Y.B.Cshared.Bshared s + Zpole s) Ω.

This file should prove that theorem from meromorphicity and principal-part
cancellation, not introduce another RH endpoint.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The current real H/E analytic target.

This theorem should eventually be proved from:
1. meromorphicity of `Zpole`;
2. meromorphicity / local principal-part description of `Y.B.Cshared.Bshared`;
3. cancellation of principal parts at every zero-pole witness;
4. holomorphy away from the pole set.
-/
theorem Harch_holomorphic_from_Bshared_Zpole_cancellation
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    -- TODO: replace these placeholders with the actual existing APIs
    -- from PrincipalPartMeromorphic / HSideResidueArithmetic / HSidePoleWitness.
    :
    HolomorphicOnC
      (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
      Ω := by
  -- This is the next real proof wall.
  -- Do not import this file into root with `sorry`.
  -- First use this target to identify the exact missing principal-part API.
  sorry

end

end RHFormalization
