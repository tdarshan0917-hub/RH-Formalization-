import RHFormalization.ShiftedLaplaceRepSummable
import RHFormalization.PrincipalPartEventuallyEq

namespace RHFormalization
noncomputable section
open Complex Filter Topology

theorem repZpole_hZpp_from_restAnalytic
    (W : ZeroWitness)
    (ρrep : ℂ)
    (hρrep_zero : IsNontrivialZetaZero ρrep)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (hρrep_mult : zetaZeroMult ρrep = zetaZeroMult W.ρ)
    (hsummable : ∀ᶠ w in 𝓝 W.s0,
      Summable (fun ρ : RepZeroIndex => zeroPoleSummand defaultZeroMultiplicityData ρ.1 w))
    (hrest :
      HolomorphicAtC
        (fun w => ∑' ρ : RepZeroIndex,
          (if ρ.1 = ρrep then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w)) W.s0) :
    HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData) W.s0
      ((defaultZeroMultiplicityData.mult W.ρ : ℂ)) := by
  classical
  set ρ0 : RepZeroIndex := ⟨ρrep, hρrep_zero, hρrep_re⟩ with hρ0
  refine ⟨(fun w => ∑' ρ : RepZeroIndex,
            (if ρ.1 = ρrep then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w)), hrest, ?_⟩
  filter_upwards [hsummable] with w hw hwz
  have hextract :
      ZpoleRepSeries defaultZeroMultiplicityData w =
        zeroPoleSummand defaultZeroMultiplicityData ρrep w +
          ∑' ρ : RepZeroIndex, (if ρ = ρ0 then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w) := by
    rw [ZpoleRepSeries]
    exact hw.tsum_eq_add_tsum_ite ρ0
  rw [hextract]
  have hsummand : zeroPoleSummand defaultZeroMultiplicityData ρrep w =
      (defaultZeroMultiplicityData.mult ρrep : ℂ) / (w - W.s0) := by
    unfold zeroPoleSummand zeroPoleDenom
    have hd : w + ρrep * (1 - ρrep) = w - W.s0 := by
      rw [← hρrep_pole]; unfold polePoint; ring
    rw [hd]
  have hite : (∑' ρ : RepZeroIndex, (if ρ = ρ0 then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w))
      = ∑' ρ : RepZeroIndex, (if ρ.1 = ρrep then 0 else zeroPoleSummand defaultZeroMultiplicityData ρ.1 w) := by
    apply tsum_congr
    intro ρ
    by_cases h : ρ = ρ0
    · simp [h, hρ0]
    · have hne : ρ.1 ≠ ρrep := by
        intro hc
        exact h (Subtype.ext hc)
      rw [if_neg h, if_neg hne]
  rw [hite, hsummand]
  have hmultNat : defaultZeroMultiplicityData.mult ρrep
      = defaultZeroMultiplicityData.mult W.ρ := by
    simp only [defaultZeroMultiplicityData]
    exact hρrep_mult
  rw [hmultNat]

#print axioms repZpole_hZpp_from_restAnalytic

end
end RHFormalization
