import RHFormalization.RepCorrectedHoloGeneric
import RHFormalization.ShiftedLaplaceModelRepHRegular
import RHFormalization.ShiftedLaplaceRepHZppFree
import RHFormalization.ShiftedLaplaceModelPP
import RHFormalization.ShiftedLaplaceModelPackageProbe
import RHFormalization.XiSummability

namespace RHFormalization
noncomputable section
open Complex Filter Topology

/-- The model B-side principal part = the proven model-PP lemma. -/
theorem model_hBpp :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC shiftedLaplaceLogDerivModel W.s0 (-(zetaZeroMult W.ρ : ℂ)) :=
  shiftedLaplaceLogDerivModel_principalPart_at_witness

/-- `h_regular` for the model raw function = the proven model Rep regularity,
once we identify `genRepRaw model` with `model + ZpoleRep`. -/
theorem model_h_regular (ZF : ZetaZeroFacts) :
    ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC (genRepRaw shiftedLaplaceLogDerivModel) z := by
  intro z hzΩ hznw
  have h := shiftedLaplaceModelRep_h_regular ZF z hzΩ hznw
  exact h

/-- **The model corrected global function is holomorphic on Ω — fully discharged.**
All three H-side inputs are proven: `hBpp` (model-PP), `hZpp_rep`
(`shiftedLaplace_hZpp_rep_free`), `h_regular` (model Rep regularity). No `hpoint`,
no keystone. -/
theorem model_repCorrectedGlobal_holomorphicOn (ZF : ZetaZeroFacts) :
    HolomorphicOnC (genRepCorrectedGlobal shiftedLaplaceLogDerivModel) Ω :=
  genRepCorrectedGlobal_holomorphicOn
    shiftedLaplaceLogDerivModel ZF
    model_hBpp
    shiftedLaplace_hZpp_rep_free
    (model_h_regular ZF)

#print axioms model_repCorrectedGlobal_holomorphicOn

end
end RHFormalization

