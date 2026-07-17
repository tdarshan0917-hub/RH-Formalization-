import RHFormalization.PuncturedMeromorphicIdentity
import RHFormalization.ShiftedLaplaceBppFromBridge
import RHFormalization.ShiftedLaplaceLogDerivIdentity
import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.OmegaConnected

namespace RHFormalization

noncomputable section

open Complex Topology Filter Set

theorem absConvRegion_eq_piece2 (s : ℂ) :
    s ∈ shiftedLaplaceAbsConvRegion ↔
      (1:ℝ) < (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)).re := by
  unfold shiftedLaplaceAbsConvRegion shiftedLaplaceSqrt
  have hhalf : ((1/2 : ℂ)).re = (1/2 : ℝ) := by norm_num
  rw [Set.mem_setOf_eq, Complex.add_re, hhalf]
  constructor <;> intro h <;> linarith

theorem shiftedLaplace_Bshared_eqOn_model (sigma0 : ℝ) :
    Set.EqOn
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      shiftedLaplaceLogDerivModel
      shiftedLaplaceAbsConvRegion := by
  intro s hs
  have hw : (1:ℝ) < (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)).re :=
    (absConvRegion_eq_piece2 s).mp hs
  have hP := shiftedLaplace_Bshared_eq_logDeriv hw
  show (shiftedLaplacePrimePackageAt sigma0).Bshared s = shiftedLaplaceLogDerivModel s
  unfold shiftedLaplaceLogDerivModel
  rw [logDeriv_apply]
  show shiftedLaplacePrimePackage.Bshared s = _
  exact hP

#print axioms shiftedLaplace_Bshared_eqOn_model

theorem shiftedLaplace_bridge_from_meromorphy
    (sigma0 : ℝ)
    (hBmero :
      MeromorphicOnC
        (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s) Ω)
    (hVopen : IsOpen shiftedLaplaceAbsConvRegion)
    (hVne : shiftedLaplaceAbsConvRegion.Nonempty)
    (hVsub : shiftedLaplaceAbsConvRegion ⊆ Ω) :
    ShiftedLaplaceBridgeData sigma0 := by
  intro W
  have hpunct :
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        =ᶠ[𝓝[≠] W.s0] shiftedLaplaceLogDerivModel :=
    meromorphic_punctured_identity
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      shiftedLaplaceLogDerivModel
      Ω shiftedLaplaceAbsConvRegion
      isPreconnected_Omega_native
      hVopen hVne hVsub
      hBmero
      shiftedLaplaceLogDerivModel_meromorphicOn_Omega
      (shiftedLaplace_Bshared_eqOn_model sigma0)
      W.s0 W.hs0_in_Omega
  have h := hpunct
  rw [Filter.EventuallyEq, nhdsWithin, Filter.eventually_inf_principal] at h
  filter_upwards [h] with w hw hwne
  exact hw hwne

#print axioms shiftedLaplace_bridge_from_meromorphy

end

end RHFormalization
