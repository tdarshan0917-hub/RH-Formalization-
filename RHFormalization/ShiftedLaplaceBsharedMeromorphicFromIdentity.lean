import RHFormalization.ShiftedLaplaceLogDerivIdentity
import RHFormalization.ShiftedLaplaceBsharedMeromorphic
import RHFormalization.OmegaConnected
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

noncomputable def shiftedClosedForm (s : ℂ) : ℂ :=
  - (1 / (2 * Complex.sqrt (s + (1/4:ℂ))))
    * (deriv riemannZeta (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))
        / riemannZeta (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)))

theorem shiftedClosedForm_meromorphicOn_Omega :
    MeromorphicOn shiftedClosedForm Ω := by
  intro s hs
  have hslit : (s + (1/4:ℂ)) ∈ Complex.slitPlane := shift_mem_slitPlane_of_mem_Omega hs
  have hne0 : (s + (1/4:ℂ)) ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hsqrt_sq : (Complex.sqrt (s + (1/4:ℂ)))^2 = s + (1/4:ℂ) := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have hsqrt_ne : Complex.sqrt (s + (1/4:ℂ)) ≠ 0 := by
    intro h
    apply hne0
    rw [← hsqrt_sq, h]; ring
  have hsqrt_an : AnalyticAt ℂ (fun z => Complex.sqrt (z + (1/4:ℂ))) s := by
    have hφ := phi_analyticAt_of_mem_Omega hs
    have hrw : (fun z => Complex.sqrt (z + (1/4:ℂ)))
        = (fun z => (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) - (1/2:ℂ)) := by
      funext z; ring
    rw [hrw]; exact hφ.sub analyticAt_const
  have hfac_an : AnalyticAt ℂ (fun z => - (1 / (2 * Complex.sqrt (z + (1/4:ℂ))))) s := by
    have h2ne : (2 : ℂ) * Complex.sqrt (s + (1/4:ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero hsqrt_ne
    have hinv : AnalyticAt ℂ (fun z => (2 * Complex.sqrt (z + (1/4:ℂ)))⁻¹) s :=
      ((analyticAt_const.mul hsqrt_an)).inv h2ne
    have hrw : (fun z => - (1 / (2 * Complex.sqrt (z + (1/4:ℂ)))))
        = (fun z => - (2 * Complex.sqrt (z + (1/4:ℂ)))⁻¹) := by
      funext z; rw [one_div]
    rw [hrw]; exact hinv.neg
  have hlog : MeromorphicAt
      (fun z => logDeriv riemannZeta (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))) s :=
    logDeriv_zeta_comp_phi_meromorphicAt hs
  have hprod : MeromorphicAt
      (fun z => (- (1 / (2 * Complex.sqrt (z + (1/4:ℂ))))) *
        logDeriv riemannZeta (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))) s :=
    hfac_an.meromorphicAt.mul hlog
  have heq : shiftedClosedForm =
      (fun z => (- (1 / (2 * Complex.sqrt (z + (1/4:ℂ))))) *
        logDeriv riemannZeta (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))) := by
    funext z
    unfold shiftedClosedForm
    rw [logDeriv_apply]
  rw [heq]; exact hprod

#print axioms shiftedClosedForm_meromorphicOn_Omega

end
end RHFormalization
