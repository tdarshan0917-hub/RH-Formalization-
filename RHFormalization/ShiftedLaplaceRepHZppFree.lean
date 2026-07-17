import RHFormalization.ShiftedLaplaceRepHZppAssembled
import RHFormalization.ShiftedLaplaceRepHZpp
import RHFormalization.ShiftedLaplaceRepZpoleResidue
import RHFormalization.ShiftedLaplaceRepDenomBound
import RHFormalization.PairPoleIsolation
import RHFormalization.XiSummability

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

/-- A rep-index `ρ'` (so `ρ'.re < 1/2`) with `ρ' ≠ ρrep` avoids both reflection-pair
members `{W.ρ, 1-W.ρ}`. (ρrep is the unique pole-fiber member with `re < 1/2`.) -/
theorem repIndex_ne_pair_of_ne_rep
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    {ρ' : ℂ} (hρ'_re : ρ'.re < 1/2) (hρ'_ne : ρ' ≠ ρrep) :
    ρ' ≠ W.ρ ∧ ρ' ≠ 1 - W.ρ := by
  constructor
  · intro hc
    apply hρ'_ne
    have hpp : polePoint ρ' = polePoint ρrep := by
      rw [hc, ← W.hs0_def]; exact hρrep_pole.symm
    rcases (polePoint_eq_iff ρ' ρrep).mp hpp with he | he
    · exact he
    · exfalso
      have hre' : ρ'.re = 1 - ρrep.re := by rw [he]; simp [Complex.sub_re, Complex.one_re]
      linarith
  · intro hc
    apply hρ'_ne
    have hpp : polePoint ρ' = polePoint ρrep := by
      have hpe : polePoint (1 - W.ρ) = polePoint W.ρ := by unfold polePoint; ring
      rw [hc, hpe, ← W.hs0_def]; exact hρrep_pole.symm
    rcases (polePoint_eq_iff ρ' ρrep).mp hpp with he | he
    · exact he
    · exfalso
      have hre' : ρ'.re = 1 - ρrep.re := by rw [he]; simp [Complex.sub_re, Complex.one_re]
      linarith

/-- The full rep-series is summable at every point of the closed witness ball.
The single `ρrep` summand is finite; the remaining terms are dominated by the
summable majorant `mult / (witnessDenomConst·(1+im²))` via `witnessDenomConst_le`. -/
theorem repZpole_summable_on_witnessBall
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_zero : IsNontrivialZetaZero ρrep)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)))
    {w : ℂ} (hw : w ∈ Metric.closedBall W.s0 R) :
    Summable (fun ρ : RepZeroIndex =>
      zeroPoleSummand defaultZeroMultiplicityData ρ.1 w) := by
  classical
  set ρ0 : RepZeroIndex := ⟨ρrep, hρrep_zero, hρrep_re⟩ with hρ0
  set c := witnessDenomConst W ρrep hρrep_re hρrep_pole R hR hRiso with hcdef
  have hcpos : 0 < c := witnessDenomConst_pos W ρrep hρrep_re hρrep_pole R hR hRiso
  -- summability is unchanged by removing the single index ρ0
  rw [← (Finset.summable_compl_iff {ρ0})]
  -- majorant on the complement
  have hrep : Summable
      ((fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
        (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)) ∘ repToFull) :=
    hsum.comp_injective repToFull_injective
  have hmaj : Summable (fun ρ : {x : RepZeroIndex // x ∉ ({ρ0} : Finset RepZeroIndex)} =>
      (1 / c) * ((defaultZeroMultiplicityData.mult (repToFull ρ.1).1 : ℝ)
        / (1 + (repToFull ρ.1).1.im ^ 2))) :=
    ((hrep.mul_left (1/c)).subtype _)
  refine Summable.of_norm_bounded hmaj ?_
  rintro ⟨ρ, hρmem⟩
  have hne : ρ.1 ≠ ρrep := by
    intro hc
    apply hρmem
    simp only [Finset.mem_singleton, hρ0]
    exact Subtype.ext hc
  have hρz : IsNontrivialZetaZero ρ.1 := ρ.2.1
  have hρre : ρ.1.re < 1/2 := ρ.2.2
  have hden := witnessDenomConst_le W ρrep hρrep_re hρrep_pole R hR hRiso ρ.1 hρz hρre hne w hw
  have hnorm : ‖zeroPoleSummand defaultZeroMultiplicityData ρ.1 w‖ =
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / ‖zeroPoleDenom ρ.1 w‖ := by
    unfold zeroPoleSummand; rw [norm_div, Complex.norm_natCast]
  rw [hnorm]
  have h1 : (0:ℝ) < 1 + ρ.1.im ^ 2 := by positivity
  have hb : (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / ‖zeroPoleDenom ρ.1 w‖ ≤
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (c * (1 + ρ.1.im ^ 2)) := by
    gcongr
  have hrfl : (repToFull ρ).1 = ρ.1 := rfl
  refine hb.trans (le_of_eq ?_)
  rw [hrfl]
  field_simp

#print axioms repIndex_ne_pair_of_ne_rep
#print axioms repZpole_summable_on_witnessBall

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

/-- **`hZpp_rep` — free-standing.** The rep-pole series has the principal part
`zetaZeroMult W.ρ / (s - W.s0)` at every zero witness `W`. Assembled from the
proven residue extraction, witness-ball summability, satisfiable rest-analyticity,
and `repZpole_hZpp_from_restAnalytic`. Unconditional (uses `hsum_unconditional`). -/
theorem shiftedLaplace_hZpp_rep_free :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)) := by
  intro W
  -- representative zero
  obtain ⟨ρrep, hρrep_zero, hρrep_re, hρrep_pole, hρrep_mult⟩ :=
    repZpole_residue_at_witness W
  -- isolation radius
  obtain ⟨r, hr, hpair⟩ := pairPole_isolated W
  set R : ℝ := r / 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  -- hRiso: 2R = r ≤ dist for non-pair zeros
  have hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0 := by
    intro ρ' hρ' hne1 hne2
    have h2R : 2 * R = r := by rw [hRdef]; ring
    rw [h2R]; exact hpair ρ' hρ' hne1 hne2
  -- hRisoRep: R ≤ dist for rep-indices ≠ ρrep (via pair exclusion)
  have hRisoRep : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ'.re < 1/2 → ρ' ≠ ρrep →
      R ≤ dist (polePoint ρ') W.s0 := by
    intro ρ' hρ' hρ're hne
    obtain ⟨hn1, hn2⟩ := repIndex_ne_pair_of_ne_rep W ρrep hρrep_re hρrep_pole hρ're hne
    have hd := hpair ρ' hρ' hn1 hn2
    rw [hRdef]; linarith
  -- hsummable on a full neighborhood (the ball)
  have hsummable : ∀ᶠ w in 𝓝 W.s0,
      Summable (fun ρ : RepZeroIndex =>
        zeroPoleSummand defaultZeroMultiplicityData ρ.1 w) := by
    have hball : Metric.closedBall W.s0 R ∈ 𝓝 W.s0 :=
      Metric.closedBall_mem_nhds W.s0 hR
    filter_upwards [hball] with w hw
    exact repZpole_summable_on_witnessBall W ρrep hρrep_zero hρrep_re hρrep_pole
      R hR hRiso hsum_unconditional hw
  -- hrest from the satisfiable witness rest-analyticity
  have hrest := repZpole_rest_analyticAt_witness_satisfiable
    W ρrep hρrep_re hρrep_pole R hR hRiso hRisoRep hsum_unconditional
  -- assemble
  have hmain := repZpole_hZpp_from_restAnalytic
    W ρrep hρrep_zero hρrep_re hρrep_pole hρrep_mult hsummable hrest
  -- coefficient: mult W.ρ = zetaZeroMult W.ρ
  have hcoeff : (defaultZeroMultiplicityData.mult W.ρ : ℂ) = (zetaZeroMult W.ρ : ℂ) := by
    rfl
  rwa [hcoeff] at hmain

#print axioms shiftedLaplace_hZpp_rep_free

end
end RHFormalization
