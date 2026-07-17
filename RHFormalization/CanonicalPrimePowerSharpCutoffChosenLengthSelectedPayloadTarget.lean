import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDLimitPayload

namespace RHFormalization

noncomputable section

/--
This is the actual remaining D-side theorem.
Do not replace these holes with more wrappers. Each hole is now real analytic content.
-/
def selectedChosenLengthDLimitPayload :
  ChosenLengthDLimitPayload :=
by
  refine
    {
      finiteOperatorLayer := ?finiteOperatorLayer
      S := ?S
      FH := ?FH
      RH := ?RH
      h_FH_holo := ?h_FH_holo
      h_RH_holo := ?h_RH_holo
      h_F_stage_to_FH := ?h_F_stage_to_FH
      h_R_stage_to_RH := ?h_R_stage_to_RH
      h_R_stage_bound := ?h_R_stage_bound
      hσ := ?hσ
    }

end

end RHFormalization
