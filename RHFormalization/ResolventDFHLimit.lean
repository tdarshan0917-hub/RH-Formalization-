import RHFormalization.CorrectedResolventPayload
import RHFormalization.ResolventOperatorLayer
import RHFormalization.PrimePowerCutoffCardDivergence
import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.EigenvalueGrowthSummable
import RHFormalization.DFHLimitConcrete
import RHFormalization.ConcreteDirichletPWQOData
import RHFormalization.CorrectedFBoundProbe
import RHFormalization.DFiniteStageOperator
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- FH = the resolvent-trace tsum over the Dirichlet eigenvalues. -/
def resolventFH : ℂ → ℂ :=
  fun s => ∑' i, (s + ((concreteDirichletPWQOData.lamShifted i : ℝ) : ℂ))⁻¹

/-- h_FH_holo via the Weyl route (lamShifted = (nπ)² satisfies n² - 0 ≤ (nπ)²). -/
theorem resolventFH_holo : HolomorphicOnC resolventFH Ω := by
  unfold resolventFH
  apply Fstage_holo_from_weyl concreteDirichletPWQOData.lamShifted
    concreteDirichletPWQOData.nonneg 1 0 one_pos
  intro n
  have : ((n:ℝ) * Real.pi)^2 = concreteDirichletPWQOData.lamShifted n := by
    unfold concreteDirichletPWQOData
    rfl
  rw [← this]
  have hpi : (1:ℝ) ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three
    nlinarith [Real.pi_pos]
  nlinarith [sq_nonneg ((n:ℝ) * Real.pi), sq_nonneg (n:ℝ)]

/-- The admissible-cutoff count diverges along the prime-power net: composition of the
proven cutoff count-divergence with `primePowerStage`'s R → ∞. -/
theorem resolventStage_card_atTop :
    Tendsto (fun n => (resolventIndices (primePowerStage n)).card) atTop atTop :=
  concretePrimePowerBelowCutoff_card_atTop.comp primePowerStage_R_tendsto_atTop

/-- The F-side convergence (h_conv on F): on every compact `K ⊆ Ω`, the staged spectral
resolvent partial `spectralResolventPartial (primePowerStage n)` converges uniformly to the
resolvent-trace tsum `resolventFH`.  Per-term majorant (banked) → Weierstrass M-test →
reindex by the diverging admissible count. -/
theorem resolvent_F_stage_to_FH :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          ∀ s : ℂ, s ∈ K →
            dist (spectralResolventPartial (primePowerStage n) s) (resolventFH s) < ε := by
  intro K hK hKOmega ε hε
  obtain ⟨CK, hCK0, hsum, hbd⟩ := resolvent_term_bound_on_compact K hK hKOmega
  have hMtest : TendstoUniformlyOn
      (fun (N : ℕ) (x : ℂ) =>
        ∑ n ∈ Finset.range N, (x + ((concreteDirichletPWQOData.lamShifted n : ℝ) : ℂ))⁻¹)
      resolventFH atTop K :=
    tendstoUniformlyOn_tsum_nat hsum hbd
  have hεN : ∀ᶠ N in atTop, ∀ x : ℂ, x ∈ K →
      dist (resolventFH x)
        (∑ n ∈ Finset.range N,
          (x + ((concreteDirichletPWQOData.lamShifted n : ℝ) : ℂ))⁻¹) < ε :=
    (Metric.tendstoUniformlyOn_iff.mp hMtest) ε hε
  have hreindex := resolventStage_card_atTop.eventually hεN
  filter_upwards [hreindex] with n hn
  intro s hs
  have h := hn s hs
  rw [dist_comm] at h
  unfold spectralResolventPartial
  exact h

/-- **The F-input — bridge input 2/4.** The concrete `DFHLimitData` for the resolvent
operator layer: `FH = resolventFH` (the trace tsum), its holomorphy `resolventFH_holo`,
and the proven compact-uniform convergence `resolvent_F_stage_to_FH` of the staged
spectral resolvent along the prime-power net.  This is exactly the `F` consumed by
`ResolventOperatorBridgeDirect`. -/
noncomputable def resolventDFHLimit :
    DFHLimitData resolventOperatorLayer.toStagePackage :=
  buildDFHLimitDataFromCompactUniform
    resolventOperatorLayer.toStagePackage
    primePowerStage
    resolventFH
    resolventFH_holo
    (by
      intro K hK hKsub ε hε
      filter_upwards [resolvent_F_stage_to_FH K hK hKsub ε hε] with n hn
      intro s hs
      exact hn s hs)
