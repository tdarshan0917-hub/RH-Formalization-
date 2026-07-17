import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.Divisor
import RHFormalization.DefaultZeroMultiplicity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# RHFormalization.ZetaCountingBound

Pillar 2 step (B): apply Mathlib's `AnalyticOnNhd.sum_divisor_le` (the zeros-from-bound
theorem) to the entire completed zeta `completedRiemannZeta₀` (= Λ₀). This is the route to
the zero-counting bound that feeds `hsum`, replacing a hand-rolled Jensen argument.

First brick: `completedRiemannZeta₀` is analytic on every closed ball (it is entire).
-/

namespace RHFormalization

open Complex Metric Set

/-- **Λ₀ is analytic on every closed ball** (it is entire, `differentiable_completedZeta₀`).
This supplies the `AnalyticOnNhd` hypothesis of `AnalyticOnNhd.sum_divisor_le`. -/
theorem completedZeta₀_analyticOnNhd (c : ℂ) (R : ℝ) :
    AnalyticOnNhd ℂ completedRiemannZeta₀ (Metric.closedBall c |R|) :=
  (differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)

#print axioms completedZeta₀_analyticOnNhd

/-- **Λ is nonvanishing for `re s > 1`.** Since `ζ(s) = Λ(s)/Γ_ℝ(s)` with `Γ_ℝ(s) ≠ 0` and
`ζ(s) ≠ 0` there, `Λ(s) ≠ 0`. -/
theorem completedZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hdef : riemannZeta s = completedRiemannZeta s / Gammaℝ s := riemannZeta_def_of_ne_zero hs0
  intro hΛ
  rw [hΛ, zero_div] at hdef
  exact hz hdef

#print axioms completedZeta_ne_zero_of_one_lt_re

open Real in
/-- `Γ_ℝ(s) = π^{-s/2} · Γ(s/2)` is analytic at every point of the open right half-plane
`{re > 0}` (there `Γ(s/2)` has no poles). -/
theorem Gammaℝ_analyticAt {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  -- The open right half-plane is a neighbourhood of s.
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hmem : s ∈ {z : ℂ | 0 < z.re} := hs
  have hnhds : {z : ℂ | 0 < z.re} ∈ nhds s := hopen.mem_nhds hmem
  -- Γ_ℝ is differentiable on the half-plane.
  have hdiff : DifferentiableOn ℂ Gammaℝ {z : ℂ | 0 < z.re} := by
    intro z hz
    have hzre : 0 < z.re := hz
    have heq : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
      funext w; exact Gammaℝ_def w
    rw [heq]
    apply DifferentiableWithinAt.mul
    · -- π^{-z/2} : const_cpow with π ≠ 0
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow
      · exact (differentiable_id.neg.div_const 2).differentiableAt
      · left; exact_mod_cast Real.pi_ne_zero
    · -- Γ(z/2) : differentiableAt_Gamma, since z/2 ≠ -m (re(z/2)=z.re/2>0)
      apply DifferentiableAt.differentiableWithinAt
      have hz2 : DifferentiableAt ℂ (fun w : ℂ => w / 2) z :=
        (differentiable_id.div_const 2).differentiableAt
      have hGamma : DifferentiableAt ℂ Complex.Gamma (z / 2) := by
        apply Complex.differentiableAt_Gamma
        intro m hcontra
        have hre2 : (z / 2).re = z.re / 2 := by
          rw [Complex.div_ofNat_re]
        rw [hcontra] at hre2
        simp only [Complex.neg_re, Complex.natCast_re] at hre2
        have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      exact hGamma.comp z hz2
  exact hdiff.analyticAt hnhds

#print axioms Gammaℝ_analyticAt

/-- On the open strip `0 < re s < 1`, `Λ = Γ_ℝ · ζ` as functions near `s` (both sides agree
wherever `s ≠ 0`, which is an open neighbourhood). -/
theorem completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[nhds s] (Gammaℝ * riemannZeta) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hnhds : {z : ℂ | 0 < z.re} ∈ nhds s := hopen.mem_nhds hs
  filter_upwards [hnhds] with w hw
  have hwre : 0 < w.re := hw
  have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at hwre; linarith
  have hG : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos hwre
  have hdef : riemannZeta w = completedRiemannZeta w / Gammaℝ w := riemannZeta_def_of_ne_zero hw0
  show completedRiemannZeta w = Gammaℝ w * riemannZeta w
  rw [hdef, mul_div_cancel₀ _ hG]

/-- **Step C (divisor correspondence):** on the open right half-plane (in particular the
critical strip), the analytic order of `Λ = completedRiemannZeta` equals that of `ζ`. Since
`Λ = Γ_ℝ·ζ` with `Γ_ℝ` analytic and nonvanishing (order 0). -/
theorem analyticOrderAt_completedZeta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt completedRiemannZeta s = analyticOrderAt riemannZeta s := by
  have hGana : AnalyticAt ℂ Gammaℝ s := Gammaℝ_analyticAt hs
  have hZana : AnalyticAt ℂ riemannZeta s := by
    have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
    have hnhds : {z : ℂ | z ≠ 1} ∈ nhds s := hopen.mem_nhds hs1
    have hdiff : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hdiff.analyticAt hnhds
  have hGorder : analyticOrderAt Gammaℝ s = 0 :=
    hGana.analyticOrderAt_eq_zero.mpr (Gammaℝ_ne_zero_of_re_pos hs)
  rw [analyticOrderAt_congr (completedZeta_eventuallyEq_mul hs),
    analyticOrderAt_mul hGana hZana, hGorder, zero_add]

#print axioms analyticOrderAt_completedZeta_eq

/-- **Λ is analytic on a closed ball that avoids the poles `0` and `1`.** Supplies the
`AnalyticOnNhd` hypothesis of `sum_divisor_le` for `f = Λ` on strip-discs. -/
theorem completedZeta_analyticOnNhd_of_avoid
    {c : ℂ} {R : ℝ} (h0 : (0:ℂ) ∉ Metric.closedBall c R) (h1 : (1:ℂ) ∉ Metric.closedBall c R) :
    AnalyticOnNhd ℂ completedRiemannZeta (Metric.closedBall c R) := by
  -- The complement of {0,1} is open and contains the closed ball.
  have hopen : IsOpen ({(0:ℂ)}ᶜ ∩ {(1:ℂ)}ᶜ : Set ℂ) :=
    (isOpen_compl_singleton).inter (isOpen_compl_singleton)
  have hsub : Metric.closedBall c R ⊆ ({(0:ℂ)}ᶜ ∩ {(1:ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    constructor
    · intro hz0; apply h0; rw [Set.mem_singleton_iff] at hz0; rw [← hz0]; exact hz
    · intro hz1; apply h1; rw [Set.mem_singleton_iff] at hz1; rw [← hz1]; exact hz
  have hdiff : DifferentiableOn ℂ completedRiemannZeta ({(0:ℂ)}ᶜ ∩ {(1:ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := hz.1
    have hz1 : z ≠ 1 := hz.2
    exact (differentiableAt_completedZeta hz0 hz1).differentiableWithinAt
  -- Analytic on the open set, restrict to the ball.
  intro z hz
  have hznhds : ({(0:ℂ)}ᶜ ∩ {(1:ℂ)}ᶜ : Set ℂ) ∈ nhds z :=
    hopen.mem_nhds (hsub hz)
  exact hdiff.analyticAt hznhds

#print axioms completedZeta_analyticOnNhd_of_avoid

open MeromorphicOn in
/-- **divisor ↔ mult bridge:** on a poles-avoiding ball, the Jensen `divisor` of `Λ` at a strip
point equals our `zetaZeroMult`. Combines `Λ`-analyticity, the divisor formula, and the step-C
order correspondence `order Λ = order ζ`. -/
theorem divisor_completedZeta_eq_mult {c : ℂ} {R : ℝ}
    (h0 : (0:ℂ) ∉ Metric.closedBall c R) (h1 : (1:ℂ) ∉ Metric.closedBall c R)
    {ρ : ℂ} (hρ : ρ ∈ Metric.closedBall c R) (hρre : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall c R) ρ = zetaZeroMult ρ := by
  rw [(completedZeta_analyticOnNhd_of_avoid h0 h1).divisor_apply hρ,
      analyticOrderAt_completedZeta_eq hρre hρ1]
  unfold zetaZeroMult
  cases analyticOrderAt riemannZeta ρ with
  | top => simp
  | coe n => simp

#print axioms divisor_completedZeta_eq_mult

end RHFormalization
