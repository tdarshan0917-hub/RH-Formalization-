import RHFormalization.GalerkinFConvergence

/-!
# RHFormalization.GalerkinDFHLimitData
**FRONT F CLOSED**: the DFHLimitData object for the genuine-operator
galerkin stage package, along alpha = galerkinStageSeq.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- **The F-object of RH_from_galerkin_F_R.** -/
def galerkinF : DFHLimitData galerkinStagePackage where
  alpha := galerkinStageSeq
  FH := galerkinFH
  h_FH_holo := galerkinFH_holo
  h_F_stage_to_FH := galerkinF_stage_to_FH

theorem galerkinF_alpha : galerkinF.alpha = galerkinStageSeq := rfl

#print axioms galerkinF
#print axioms galerkinF_alpha

end

end RHFormalization
