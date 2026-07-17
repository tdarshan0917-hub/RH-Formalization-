import RHFormalization.ResolventOperatorLayer
import RHFormalization.ResolventStageConvergence
import RHFormalization.ConcreteResolventConvergence
import RHFormalization.ResolventLocalBound

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- The resolvent partial sums converge uniformly on any ball ⊆ Ω to the full
    resolvent tsum, for the concrete Dirichlet spectrum. Direct instance of the
    proven resolvent_partialSums_tendstoUniformlyOn_ball at λ_k = (kπ)². -/
theorem spectralResolvent_tendstoUniformlyOn_ball
    (c : ℂ) (r : ℝ)
    (u : ℕ → ℝ) (hu : Summable u)
    (hbd : ∀ n, ∀ s ∈ Metric.ball c r,
      ‖(s + ((concreteDirichletPWQOData.lamShifted n : ℝ) : ℂ))⁻¹‖ ≤ u n) :
    TendstoUniformlyOn
      (fun (N : ℕ) (s : ℂ) =>
        ∑ i ∈ Finset.range N, (s + ((concreteDirichletPWQOData.lamShifted i : ℝ) : ℂ))⁻¹)
      (fun s => ∑' i, (s + ((concreteDirichletPWQOData.lamShifted i : ℝ) : ℂ))⁻¹)
      atTop (Metric.ball c r) :=
  resolvent_partialSums_tendstoUniformlyOn_ball
    (fun n => concreteDirichletPWQOData.lamShifted n) c r u hu hbd

#print axioms spectralResolvent_tendstoUniformlyOn_ball

end
end RHFormalization
