import RHFormalization.PrimeSideStieltjesLaplaceKernel
import Mathlib

set_option autoImplicit false
namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

theorem shifted_mem_slitPlane {s : ℂ} (hs : s ∈ Ω) :
    shiftedSpectralParameter s ∈ slitPlane := by
  rw [mem_Omega_iff] at hs
  unfold shiftedSpectralParameter
  rw [Complex.mem_slitPlane_iff]
  by_cases him : s.im = 0
  · left
    have : ¬ (s.re ≤ 0) := fun h => hs ⟨him, h⟩
    push_neg at this
    simp [Complex.add_re, him]; linarith
  · right
    simp [Complex.add_im, him]

theorem stieltjesLaplaceKernelCore_analyticAt
    (a : ℝ) {s : ℂ} (hs : s ∈ Ω) :
    AnalyticAt ℂ (fun z => stieltjesLaplaceKernelCore a z) s := by
  have hslit : shiftedSpectralParameter s ∈ slitPlane := shifted_mem_slitPlane hs
  have hshift : AnalyticAt ℂ (fun z => shiftedSpectralParameter z) s := by
    unfold shiftedSpectralParameter
    exact analyticAt_id.add analyticAt_const
  have hsqrt : AnalyticAt ℂ (fun z => Complex.sqrt (shiftedSpectralParameter z)) s := by
    have hsqrtAt : AnalyticAt ℂ Complex.sqrt (shiftedSpectralParameter s) :=
      (differentiableAt_sqrt hslit).analyticAt
    exact hsqrtAt.comp hshift
  have hzne : shiftedSpectralParameter s ≠ 0 := slitPlane_ne_zero hslit
  have hne : Complex.sqrt (shiftedSpectralParameter s) ≠ 0 := by
    intro h
    apply hzne
    have key : Complex.sqrt (shiftedSpectralParameter s) * Complex.sqrt (shiftedSpectralParameter s)
        = shiftedSpectralParameter s := Complex.mul_self_sqrt (shiftedSpectralParameter s)
    rw [h, mul_zero] at key
    exact key.symm
  have hinv : AnalyticAt ℂ (fun z => (Complex.sqrt (shiftedSpectralParameter z))⁻¹) s :=
    hsqrt.inv hne
  have hexp : AnalyticAt ℂ
      (fun z => Complex.exp (-(a : ℂ) * Complex.sqrt (shiftedSpectralParameter z))) s := by
    have hmul : AnalyticAt ℂ
        (fun z => -(a : ℂ) * Complex.sqrt (shiftedSpectralParameter z)) s :=
      analyticAt_const.mul hsqrt
    exact analyticAt_cexp.comp hmul
  have hprod := ((analyticAt_const (v := (1/2 : ℂ))).mul hinv).mul hexp
  refine hprod.congr ?_
  filter_upwards with z
  simp only [Pi.mul_apply]
  unfold stieltjesLaplaceKernelCore
  ring

#print axioms stieltjesLaplaceKernelCore_analyticAt
