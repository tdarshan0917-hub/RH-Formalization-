import RHFormalization.ShiftedLaplaceBranchRange
import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.MeromorphyAssembly
import RHFormalization.ZetaLogDerivPrincipalPart
import Mathlib

namespace RHFormalization

noncomputable section
open Complex Set Topology Filter

/-- `logDeriv ζ` is analytic at `ρ` whenever `ρ ≠ 1` and `ζ(ρ) ≠ 0`. -/
theorem logDeriv_zeta_analyticAt {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : riemannZeta ρ ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta) ρ := by
  have hζ : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρ1
  have hderiv : AnalyticAt ℂ (deriv riemannZeta) ρ := hζ.deriv
  have hdiv : AnalyticAt ℂ (fun z => deriv riemannZeta z / riemannZeta z) ρ :=
    hderiv.div hζ hρ0
  simpa only [logDeriv] using hdiv

/-- **The model is analytic at any `z ∈ Ω` where `ζ(φ z) ≠ 0`.** -/
theorem model_analyticAt_of_zeta_ne_zero {z : ℂ} (hzΩ : z ∈ Ω)
    (hζ : riemannZeta (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) ≠ 0) :
    AnalyticAt ℂ shiftedLaplaceLogDerivModel z := by
  have hmer : MeromorphicAt shiftedLaplaceLogDerivModel z :=
    shiftedLaplaceLogDerivModel_meromorphicOn_Omega z hzΩ
  apply hmer.analyticAt
  have hne1 : (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) ≠ 1 :=
    phi_ne_one_of_mem_Omega hzΩ
  -- continuity of each piece, combined with fun_prop where possible
  have hlogan : AnalyticAt ℂ (logDeriv riemannZeta)
      (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) :=
    logDeriv_zeta_analyticAt hne1 hζ
  have hlogc : ContinuousAt (logDeriv riemannZeta)
      (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) := hlogan.continuousAt
  have hφc : ContinuousAt (fun w : ℂ => Complex.sqrt (w + (1/4:ℂ)) + (1/2:ℂ)) z :=
    (phi_differentiableAt_of_mem_Omega hzΩ).continuousAt
  -- compose via comp' (no definitional point-match required)
  have hcompc : ContinuousAt
      (fun w => logDeriv riemannZeta (Complex.sqrt (w + (1/4:ℂ)) + (1/2:ℂ))) z := by
    exact ContinuousAt.comp' hlogc hφc
  have hprec : ContinuousAt (fun w => -(1 / (2 * Complex.sqrt (w + (1/4:ℂ))))) z :=
    (prefactor_analyticAt_of_mem_Omega hzΩ).continuousAt
  have hmulc : ContinuousAt
      (fun w => (-(1 / (2 * Complex.sqrt (w + (1/4:ℂ)))))
          * logDeriv riemannZeta (Complex.sqrt (w + (1/4:ℂ)) + (1/2:ℂ))) z :=
    hprec.mul hcompc
  have hmodel_eq : shiftedLaplaceLogDerivModel
      = fun w => (-(1 / (2 * Complex.sqrt (w + (1/4:ℂ)))))
          * logDeriv riemannZeta (Complex.sqrt (w + (1/4:ℂ)) + (1/2:ℂ)) := by
    funext w; unfold shiftedLaplaceLogDerivModel; ring
  rw [hmodel_eq]
  exact hmulc

/-- **THE GATE: `hB_regular` for the model.** -/
theorem shiftedLaplaceModel_regular
    (z : ℂ) (hzΩ : z ∈ Ω) (hznw : ∀ W : ZeroWitness, z ≠ W.s0) :
    AnalyticAt ℂ shiftedLaplaceLogDerivModel z := by
  set ρ : ℂ := Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ) with hρdef
  by_cases hζ : riemannZeta ρ = 0
  · exfalso
    have hre_ge : (1/2:ℝ) ≤ ρ.re := phi_re_ge_half z
    have hre_pos : 0 < ρ.re := by linarith
    have hρ1 : ρ ≠ 1 := phi_ne_one_of_mem_Omega hzΩ
    have hre_lt : ρ.re < 1 := by
      by_contra hge
      push_neg at hge
      exact (riemannZeta_ne_zero_of_one_le_re hge) hζ
    have hnz : IsNontrivialZetaZero ρ := ⟨hζ, hre_pos, hre_lt⟩
    have hzpp : z = polePoint ρ := polePoint_of_phi_eq hρdef.symm
    have hΩρ : polePoint ρ ∈ Ω := hzpp ▸ hzΩ
    have hoff : IsOffCritical ρ := offCritical_of_polePoint_mem_Omega ρ hnz hΩρ
    let W : ZeroWitness := ⟨ρ, hnz, hoff, z, hzpp, hzΩ⟩
    exact hznw W rfl
  · exact model_analyticAt_of_zeta_ne_zero hzΩ hζ

#print axioms shiftedLaplaceModel_regular

end
end RHFormalization
