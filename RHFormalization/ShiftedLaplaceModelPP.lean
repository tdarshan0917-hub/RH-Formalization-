import RHFormalization.ShiftedLaplaceResidueArith
import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.PrincipalPartConstMul
import RHFormalization.PrincipalPartTransport
import RHFormalization.ZetaLogDerivPrincipalPart
import RHFormalization.ZetaMultReflection
import RHFormalization.ShiftedLaplaceBsharedMeromorphic

namespace RHFormalization

open Complex

/-- `logDeriv ζ` has a simple pole at a zero `ρ` with residue exactly
`zetaZeroMult ρ` (the analytic order). -/
theorem zeta_logDeriv_pp_zetaZeroMult
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : riemannZeta ρ = 0) :
    HasPrincipalPartAtC (logDeriv riemannZeta) ρ (zetaZeroMult ρ : ℂ) := by
  have hAn : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρ1
  have hneTop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; exact riemannZeta_not_eventually_zero hρ1
  have hk_cast : analyticOrderAt riemannZeta ρ = (zetaZeroMult ρ : ℕ) := by
    unfold zetaZeroMult
    rw [← Nat.cast_analyticOrderNatAt hneTop]
    rfl
  exact logDeriv_hasPrincipalPart_at_zero hAn hk_cast

/-- The model equals `prefactor · (logDeriv ζ ∘ shiftedPhi)` pointwise. -/
theorem model_eq_prefactor_mul (s : ℂ) :
    shiftedLaplaceLogDerivModel s
      = (-(1 / (2 * Complex.sqrt (s + (1/4:ℂ)))))
        * logDeriv riemannZeta (shiftedPhi s) := by
  unfold shiftedLaplaceLogDerivModel shiftedPhi
  ring

/-- **Model principal part, case `re ρ > 1/2`.** -/
theorem model_principalPart_at_witness_re_gt
    {ρ : ℂ} (h : (1/2:ℝ) < ρ.re) (hρ1 : ρ ≠ 1) (hρ0 : riemannZeta ρ = 0)
    (hΩ : polePoint ρ ∈ Ω) :
    HasPrincipalPartAtC shiftedLaplaceLogDerivModel (polePoint ρ)
      (-(zetaZeroMult ρ : ℂ)) := by
  -- logDeriv ζ principal part at ρ, residue zetaZeroMult ρ
  have hpp := zeta_logDeriv_pp_zetaZeroMult hρ1 hρ0
  -- φ analytic, φ(s0)=ρ, φ'(s0)≠0
  have hφan : AnalyticAt ℂ shiftedPhi (polePoint ρ) :=
    phi_analyticAt_of_mem_Omega hΩ
  have hφeq : shiftedPhi (polePoint ρ) = ρ := phi_polePoint_eq_of_re_gt h
  have hφ' : deriv shiftedPhi (polePoint ρ) ≠ 0 :=
    shiftedPhi_deriv_ne_zero_of_mem_Omega hΩ
  -- transport: logDeriv ζ ∘ φ has residue (zetaZeroMult ρ)/φ'(s0)
  have hcomp : HasPrincipalPartAtC (fun w => logDeriv riemannZeta (shiftedPhi w))
      (polePoint ρ) ((zetaZeroMult ρ : ℂ) / deriv shiftedPhi (polePoint ρ)) :=
    hasPrincipalPart_comp hpp hφan hφeq hφ'
  -- multiply by prefactor
  have hpre : AnalyticAt ℂ (fun w => -(1 / (2 * Complex.sqrt (w + (1/4:ℂ))))) (polePoint ρ) :=
    prefactor_analyticAt_of_mem_Omega hΩ
  have hmul := hasPrincipalPart_const_mul hcomp hpre
  -- residue from hmul: prefactor(s0) * ((zetaZeroMult ρ)/φ'(s0))
  -- simplify to -(zetaZeroMult ρ) using the -1 cancellation
  have hcancel := prefactor_div_phiDeriv_eq_neg_one_of_re_gt h hΩ
  have hres : (-(1 / (2 * Complex.sqrt (polePoint ρ + (1/4:ℂ)))))
      * ((zetaZeroMult ρ : ℂ) / deriv shiftedPhi (polePoint ρ))
      = -(zetaZeroMult ρ : ℂ) := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, hcancel, mul_neg, mul_one]
  -- align model with prefactor * (logDeriv ζ ∘ φ)
  have hmodel_eq : shiftedLaplaceLogDerivModel
      = fun w => (-(1 / (2 * Complex.sqrt (w + (1/4:ℂ)))))
          * logDeriv riemannZeta (shiftedPhi w) := by
    funext w; exact model_eq_prefactor_mul w
  rw [hmodel_eq, ← hres]
  exact hmul

/-- **Model principal part, case `re ρ < 1/2`.** Branch lands on `1-ρ`;
multiplicity symmetry gives residue `-(zetaZeroMult ρ)`. -/
theorem model_principalPart_at_witness_re_lt
    {ρ : ℂ} (h : ρ.re < (1/2:ℝ)) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ0 : riemannZeta ρ = 0) (hΩ : polePoint ρ ∈ Ω) :
    HasPrincipalPartAtC shiftedLaplaceLogDerivModel (polePoint ρ)
      (-(zetaZeroMult ρ : ℂ)) := by
  -- 1 - ρ is a nontrivial zero
  have hrefl : IsNontrivialZetaZero (1 - ρ) := reflected_zero ρ ⟨hρ0, h0, h1⟩
  obtain ⟨hz', h0', h1'⟩ := hrefl
  have hsub1 : (1 - ρ) ≠ 1 := by
    intro hc
    have : ρ = 0 := by have := congrArg (fun z => 1 - z) hc; simpa using this
    rw [this] at h0; simp at h0
  -- logDeriv ζ pole at 1-ρ, residue zetaZeroMult (1-ρ)
  have hpp := zeta_logDeriv_pp_zetaZeroMult hsub1 hz'
  -- φ(s0) = 1 - ρ
  have hφan : AnalyticAt ℂ shiftedPhi (polePoint ρ) :=
    phi_analyticAt_of_mem_Omega hΩ
  have hφeq : shiftedPhi (polePoint ρ) = 1 - ρ := phi_polePoint_eq_of_re_lt h
  have hφ' : deriv shiftedPhi (polePoint ρ) ≠ 0 :=
    shiftedPhi_deriv_ne_zero_of_mem_Omega hΩ
  have hcomp : HasPrincipalPartAtC (fun w => logDeriv riemannZeta (shiftedPhi w))
      (polePoint ρ) ((zetaZeroMult (1 - ρ) : ℂ) / deriv shiftedPhi (polePoint ρ)) :=
    hasPrincipalPart_comp hpp hφan hφeq hφ'
  have hpre : AnalyticAt ℂ (fun w => -(1 / (2 * Complex.sqrt (w + (1/4:ℂ))))) (polePoint ρ) :=
    prefactor_analyticAt_of_mem_Omega hΩ
  have hmul := hasPrincipalPart_const_mul hcomp hpre
  have hcancel := prefactor_div_phiDeriv_eq_neg_one_of_re_lt h hΩ
  -- multiplicity symmetry: zetaZeroMult (1-ρ) = zetaZeroMult ρ
  have hsym : zetaZeroMult (1 - ρ) = zetaZeroMult ρ := (zetaZeroMult_reflection h0 h1).symm
  have hres : (-(1 / (2 * Complex.sqrt (polePoint ρ + (1/4:ℂ)))))
      * ((zetaZeroMult (1 - ρ) : ℂ) / deriv shiftedPhi (polePoint ρ))
      = -(zetaZeroMult ρ : ℂ) := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, hcancel, mul_neg, mul_one, hsym]
  have hmodel_eq : shiftedLaplaceLogDerivModel
      = fun w => (-(1 / (2 * Complex.sqrt (w + (1/4:ℂ)))))
          * logDeriv riemannZeta (shiftedPhi w) := by
    funext w; exact model_eq_prefactor_mul w
  rw [hmodel_eq, ← hres]
  exact hmul

/-- **Unified model principal part at any witness.** -/
theorem shiftedLaplaceLogDerivModel_principalPart_at_witness
    (W : ZeroWitness) :
    HasPrincipalPartAtC shiftedLaplaceLogDerivModel W.s0
      (-(zetaZeroMult W.ρ : ℂ)) := by
  obtain ⟨hz, h0, h1⟩ := W.h_zero
  have hoff : W.ρ.re ≠ (1/2:ℝ) := W.h_offline
  have hΩ : polePoint W.ρ ∈ Ω := by rw [← W.hs0_def]; exact W.hs0_in_Omega
  rw [W.hs0_def]
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact model_principalPart_at_witness_re_lt hlt h0 h1 hz hΩ
  · have hρ1 : W.ρ ≠ 1 := by intro hc; rw [hc] at h1; simp at h1
    exact model_principalPart_at_witness_re_gt hgt hρ1 hz hΩ

end RHFormalization

