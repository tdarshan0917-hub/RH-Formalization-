/-
Pillar (c), witness case: at each W.s0, HarchΩ = model + ZpoleRepSeries has a
punctured-local holomorphic extension — model PP (−mult) cancels rep PP (+mult).
-/
import RHFormalization.ShiftedLaplaceHarchOmega
import RHFormalization.ShiftedLaplaceModelPP
import RHFormalization.ShiftedLaplaceRepHZpp
import RHFormalization.ShiftedLaplaceRepHZppAssembled
import RHFormalization.ShiftedLaplaceRepHZppFree
import RHFormalization.PairPoleIsolation
import RHFormalization.HsumUnconditional

namespace RHFormalization

noncomputable section

open Complex Filter Topology Metric

/-- Generic cancellation: opposite principal parts at `z` make the sum extend
holomorphically across `z` (punctured equality). -/
theorem pp_cancel_localExt
    (f g : ℂ → ℂ) (z c : ℂ)
    (hf : HasPrincipalPartAtC f z c)
    (hg : HasPrincipalPartAtC g z (-c)) :
    ∃ h : ℂ → ℂ, HolomorphicAtC h z ∧
      (∀ᶠ w in 𝓝 z, w ≠ z → f w + g w = h w) := by
  obtain ⟨hf_reg, hf_holo, hf_eq⟩ := hf
  obtain ⟨hg_reg, hg_holo, hg_eq⟩ := hg
  refine ⟨fun w => hf_reg w + hg_reg w, hf_holo.add hg_holo, ?_⟩
  filter_upwards [hf_eq, hg_eq] with w hfw hgw hwne
  have hd : w - z ≠ 0 := sub_ne_zero.mpr hwne
  rw [hfw hwne, hgw hwne]
  field_simp
  ring

/-- The ZpoleRepSeries has principal part `+mult(W.ρ)` at every witness —
unconditional (pillar-(b) powered). -/
theorem zpoleRepSeries_pp_at_witness (W : ZeroWitness) :
    HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData) W.s0
      ((defaultZeroMultiplicityData.mult W.ρ : ℂ)) := by
  classical
  obtain ⟨ρrep, hρrep_zero, hρrep_re, hρrep_pole, hρrep_mult⟩ :=
    repZpole_residue_at_witness W
  obtain ⟨r, hr, hriso⟩ := pairPole_isolated W
  set R : ℝ := r / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0 := by
    intro ρ' h1 h2 h3
    have := hriso ρ' h1 h2 h3
    rw [hRdef]; linarith
  -- ρrep is a member of the reflection pair
  have hq : (ρrep - W.ρ) * (ρrep - (1 - W.ρ)) = 0 := by
    have h1 : polePoint ρrep = polePoint W.ρ := by
      rw [hρrep_pole, W.hs0_def]
    unfold polePoint at h1
    have h2 : ρrep * (1 - ρrep) = W.ρ * (1 - W.ρ) := neg_injective h1
    linear_combination -h2
  have hRisoRep : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ'.re < 1/2 → ρ' ≠ ρrep →
      R ≤ dist (polePoint ρ') W.s0 := by
    intro ρ' hnz' hre' hne'
    by_cases hpair1 : ρ' = W.ρ
    · exfalso
      rcases mul_eq_zero.mp hq with h | h
      · exact hne' (by rw [hpair1, ← sub_eq_zero.mp h])
      · have hrepeq : ρrep = 1 - W.ρ := sub_eq_zero.mp h
        have hrre : ρrep.re = 1 - W.ρ.re := by
          rw [hrepeq]; simp [Complex.sub_re, Complex.one_re]
        have hWre : ρ'.re = W.ρ.re := by rw [hpair1]
        rw [hrre] at hρrep_re
        rw [hWre] at hre'
        linarith
    · by_cases hpair2 : ρ' = 1 - W.ρ
      · exfalso
        rcases mul_eq_zero.mp hq with h | h
        · have hrepeq : ρrep = W.ρ := sub_eq_zero.mp h
          have h1 : ρ'.re = 1 - W.ρ.re := by
            rw [hpair2]; simp [Complex.sub_re, Complex.one_re]
          rw [hrepeq] at hρrep_re
          rw [h1] at hre'
          linarith
        · exact hne' (by rw [hpair2, ← sub_eq_zero.mp h])
      · have h2R := hRiso ρ' hnz' hpair1 hpair2
        linarith
  have hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)) :=
    hsum_from_bandCount_summable summable_bandTotal_weighted
  have hsummable : ∀ᶠ w in 𝓝 W.s0,
      Summable (fun ρ : RepZeroIndex =>
        zeroPoleSummand defaultZeroMultiplicityData ρ.1 w) :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds W.s0 hR)
      (fun w hw => repZpole_summable_on_witnessBall
        W ρrep hρrep_zero hρrep_re hρrep_pole R hR hRiso hsum hw)
  have hrest : HolomorphicAtC
      (fun w => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0
          else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w)) W.s0 :=
    repZpole_rest_analyticAt_witness_satisfiable
      W ρrep hρrep_re hρrep_pole R hR hRiso hRisoRep hsum
  exact repZpole_hZpp_from_restAnalytic
    W ρrep hρrep_zero hρrep_re hρrep_pole hρrep_mult hsummable hrest

/-- **Pillar (c), witness case.** At every witness, HarchΩ has a
punctured-local holomorphic extension. Unconditional. -/
theorem shiftedLaplaceHarchOmega_localExt_at_witness (W : ZeroWitness) :
    ∃ h : ℂ → ℂ, HolomorphicAtC h W.s0 ∧
      (∀ᶠ w in 𝓝 W.s0, w ≠ W.s0 → shiftedLaplaceHarchOmega w = h w) := by
  have hmodel : HasPrincipalPartAtC shiftedLaplaceLogDerivModel W.s0
      (-(zetaZeroMult W.ρ : ℂ)) :=
    shiftedLaplaceLogDerivModel_principalPart_at_witness W
  have hZ : HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData) W.s0
      (-(-(zetaZeroMult W.ρ : ℂ))) := by
    rw [neg_neg]
    exact zpoleRepSeries_pp_at_witness W
  obtain ⟨h, hholo, heq⟩ :=
    pp_cancel_localExt shiftedLaplaceLogDerivModel
      (ZpoleRepSeries defaultZeroMultiplicityData) W.s0
      (-(zetaZeroMult W.ρ : ℂ)) hmodel hZ
  exact ⟨h, hholo, heq⟩

#print axioms zpoleRepSeries_pp_at_witness
#print axioms shiftedLaplaceHarchOmega_localExt_at_witness

end

end RHFormalization
