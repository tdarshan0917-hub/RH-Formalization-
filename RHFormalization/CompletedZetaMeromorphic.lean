import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Brick A — `completedRiemannZeta₀` as a `MeromorphicOn` function

`Λ₀` is entire (`differentiable_completedZeta₀`), hence analytic, hence meromorphic
on every closed ball. This wraps it in the exact form the Jensen keystone
`MeromorphicOn.circleAverage_log_norm` consumes, so the zero-count-in-disk bound
(Brick C) can be assembled.
-/

namespace RHFormalization
open Complex Metric

/-- `Λ₀` is analytic everywhere (entire), via Cauchy: differentiable on the open `univ`. -/
theorem completedZeta₀_analyticOnNhd :
    AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
  differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ

/-- `Λ₀` is meromorphic on every closed ball — the hypothesis the Jensen keystone wants. -/
theorem completedZeta₀_meromorphicOn (c : ℂ) (R : ℝ) :
    MeromorphicOn completedRiemannZeta₀ (closedBall c |R|) :=
  (completedZeta₀_analyticOnNhd.mono (Set.subset_univ _)).meromorphicOn

#print axioms completedZeta₀_analyticOnNhd
#print axioms completedZeta₀_meromorphicOn

/-- `Λ₀` is meromorphic (globally) — `∀ x, MeromorphicAt`. -/
theorem completedZeta₀_meromorphic : Meromorphic completedRiemannZeta₀ := by
  intro x
  exact (completedZeta₀_analyticOnNhd x (Set.mem_univ x)).meromorphicAt

open Filter Function MeromorphicOn Metric Real Set in
/-- **Brick C — Jensen identity for the completed zeta.**
The logarithmic counting function of `Λ₀`'s zero divisor equals the circle average of
`log‖Λ₀‖` minus a constant. Direct instantiation of Mathlib's packaged Jensen reformulation.
The LHS is the weighted zero count; bounding the RHS (Brick B) bounds the zero count. -/
theorem completedZeta₀_logCounting_eq {R : ℝ} (hR : R ≠ 0) :
    Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor completedRiemannZeta₀ Set.univ) R
      = circleAverage (fun z => Real.log ‖completedRiemannZeta₀ z‖) 0 R
        - Real.log ‖meromorphicTrailingCoeffAt completedRiemannZeta₀ 0‖ :=
  Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
    completedZeta₀_meromorphic hR

end RHFormalization

