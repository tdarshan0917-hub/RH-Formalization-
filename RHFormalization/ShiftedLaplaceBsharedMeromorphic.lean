import RHFormalization.ShiftedLaplaceLogDerivIdentity
import RHFormalization.ZetaLogDerivPrincipalPart
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace RHFormalization

open Complex Filter Topology

/-- For `s ∈ Ω`, the shifted argument `s + 1/4` lies in the slit plane. -/
theorem shift_mem_slitPlane_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    (s + (1/4:ℂ)) ∈ Complex.slitPlane := by
  rw [mem_slitPlane_iff]
  rw [mem_Omega_iff] at hs
  by_cases him : s.im = 0
  · left
    have hre : ¬ (s.re ≤ 0) := fun h => hs ⟨him, h⟩
    push_neg at hre
    have : (s + (1/4:ℂ)).re = s.re + 1/4 := by
      simp [Complex.add_re]
    rw [this]; linarith
  · right
    have : (s + (1/4:ℂ)).im = s.im := by simp [Complex.add_im]
    rw [this]; exact him

/-- `φ s = √(s+1/4) + 1/2` is differentiable at every point of Ω. -/
theorem phi_differentiableAt_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    DifferentiableAt ℂ (fun z => Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) s := by
  have hslit : (s + (1/4:ℂ)) ∈ Complex.slitPlane := shift_mem_slitPlane_of_mem_Omega hs
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z + (1/4:ℂ)) s :=
    (differentiableAt_id).add_const _
  have hsqrt : DifferentiableAt ℂ Complex.sqrt (s + (1/4:ℂ)) :=
    Complex.differentiableAt_sqrt hslit
  exact (hsqrt.comp s hshift).add_const _

/-- `φ` is analytic at every point of Ω. -/
theorem phi_analyticAt_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    AnalyticAt ℂ (fun z => Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) s := by
  -- φ is differentiable on the open set Ω' := preimage; use DifferentiableOn.analyticAt on slitPlane-shift
  have hopen : IsOpen {z : ℂ | (z + (1/4:ℂ)) ∈ Complex.slitPlane} :=
    isOpen_slitPlane.preimage (by fun_prop)
  have hmem : s ∈ {z : ℂ | (z + (1/4:ℂ)) ∈ Complex.slitPlane} :=
    shift_mem_slitPlane_of_mem_Omega hs
  have hdiff : DifferentiableOn ℂ
      (fun z => Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))
      {z : ℂ | (z + (1/4:ℂ)) ∈ Complex.slitPlane} := by
    intro z hz
    exact (phi_differentiableAt_of_mem_Omega_aux hz).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hmem)
where
  phi_differentiableAt_of_mem_Omega_aux {z : ℂ}
      (hz : z ∈ {w : ℂ | (w + (1/4:ℂ)) ∈ Complex.slitPlane}) :
      DifferentiableAt ℂ (fun w => Complex.sqrt (w + (1/4:ℂ)) + (1/2:ℂ)) z := by
    have hshift : DifferentiableAt ℂ (fun w : ℂ => w + (1/4:ℂ)) z :=
      (differentiableAt_id).add_const _
    exact ((Complex.differentiableAt_sqrt hz).comp z hshift).add_const _


/-- For `s ∈ Ω`, `φ s ≠ 1` (since `φ s = 1` forces `s = 0 ∉ Ω`). -/
theorem phi_ne_one_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) ≠ (1:ℂ) := by
  intro heq
  have hsqrt : Complex.sqrt (s + (1/4:ℂ)) = (1/2:ℂ) := by linear_combination heq
  -- square both sides via (z^(2⁻¹))^2 = z
  have hsq : s + (1/4:ℂ) = (1/2:ℂ)^2 := by
    have hpow : (Complex.sqrt (s + (1/4:ℂ)))^2 = s + (1/4:ℂ) := by
      unfold Complex.sqrt
      exact Complex.cpow_nat_inv_pow _ (by norm_num)
    rw [hsqrt] at hpow
    linear_combination - hpow
  have hs0 : s = 0 := by
    have : s = (1/2:ℂ)^2 - (1/4:ℂ) := by linear_combination hsq
    rw [this]; ring
  rw [mem_Omega_iff] at hs
  exact hs (by rw [hs0]; exact ⟨by simp, by simp⟩)

/-- `logDeriv ζ ∘ φ` is meromorphic at each point of Ω (φ avoids the ζ-pole at 1). -/
theorem logDeriv_zeta_comp_phi_meromorphicAt {s : ℂ} (hs : s ∈ Ω) :
    MeromorphicAt
      (fun z => logDeriv riemannZeta (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))) s := by
  have hφ : AnalyticAt ℂ (fun z => Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)) s :=
    phi_analyticAt_of_mem_Omega hs
  have hne : (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) ≠ 1 := phi_ne_one_of_mem_Omega hs
  have hζan : AnalyticAt ℂ riemannZeta (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) :=
    analyticAt_riemannZeta hne
  have hζmer : MeromorphicAt riemannZeta (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) :=
    hζan.meromorphicAt
  have hlog : MeromorphicAt (logDeriv riemannZeta)
      (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) := by
    have hd : MeromorphicAt (fun z => deriv riemannZeta z / riemannZeta z)
        (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) := hζmer.deriv.div hζmer
    simpa only [logDeriv] using hd
  have hcomp :=
    MeromorphicAt.comp_analyticAt
      (f := logDeriv riemannZeta)
      (g := fun z => Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))
      hlog hφ
  simpa [Function.comp_def] using hcomp

/-- **B-side continuation candidate is meromorphic on Ω**, sourced from ζ. -/
theorem logDeriv_zeta_comp_phi_meromorphicOn_Omega :
    MeromorphicOn
      (fun z => logDeriv riemannZeta (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))) Ω :=
  fun s hs => logDeriv_zeta_comp_phi_meromorphicAt hs

end RHFormalization
