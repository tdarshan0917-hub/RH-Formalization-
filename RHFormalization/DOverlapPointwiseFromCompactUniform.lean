import RHFormalization.DOverlapFromStageSplitLimits
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualConcrete
import RHFormalization.HalfPlaneGeometry

/-!
# RHFormalization.DOverlapPointwiseFromCompactUniform

Pointwise convergence adapters from the compact-uniform convergence fields in
`DFHLimitData` and `DMasterResidualData`.

These adapters are used to feed `DOverlapIdentityAPI_from_pointwise_stage_limits`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped Topology

/--
Pointwise F-stage convergence from compact-uniform F convergence,
assuming the relevant right half-plane lies in Ω.
-/
theorem DFHLimitData.pointwise_F_stage_tendsto_of_RHP_subset_Omega
    {P : DFiniteStagePackage}
    (F : DFHLimitData P)
    (hRHP : RightHalfPlane P.sigma0 ⊆ Ω) :
    ∀ s ∈ RightHalfPlane P.sigma0,
      Filter.Tendsto
        (fun n : ℕ => P.F_stage (F.alpha n) s)
        Filter.atTop
        (nhds (F.FH s)) := by
  intro s hs
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsingle : ({s} : Set ℂ) ⊆ Ω := by
    intro z hz
    have hz' : z = s := by
      simpa using hz
    subst z
    exact hRHP hs
  have h :=
    F.compact_uniform_F_stage_convergence
      ({s} : Set ℂ)
      isCompact_singleton
      hsingle
      ε
      hε
  exact h.mono (by
    intro n hn
    exact hn s (by simp))

/--
Pointwise R-stage convergence from compact-uniform residual convergence,
assuming the relevant right half-plane lies in Ω.
-/
theorem DMasterResidualData.pointwise_R_stage_tendsto_of_RHP_subset_Omega
    {P : DFiniteStagePackage}
    (R : DMasterResidualData P)
    (hRHP : RightHalfPlane P.sigma0 ⊆ Ω) :
    ∀ s ∈ RightHalfPlane P.sigma0,
      Filter.Tendsto
        (fun n : ℕ => P.R_stage (R.alpha n) s)
        Filter.atTop
        (nhds (R.RH s)) := by
  intro s hs
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsingle : ({s} : Set ℂ) ⊆ Ω := by
    intro z hz
    have hz' : z = s := by
      simpa using hz
    subst z
    exact hRHP hs
  have h :=
    R.compact_uniform_residual_convergence
      ({s} : Set ℂ)
      isCompact_singleton
      hsingle
      ε
      hε
  exact h.mono (by
    intro n hn
    exact hn s (by simp))

end

end RHFormalization
